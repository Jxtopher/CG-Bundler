use proc_macro2::{TokenStream, TokenTree};
use quote::quote;
use std::collections::{HashMap, HashSet};
use syn::{
    visit::{self, Visit},
    visit_mut::{self, VisitMut},
    Field, File, Ident, ItemEnum, ItemFn, ItemMod, ItemStruct, ItemTrait, ItemUse, Macro, PatIdent,
    UseTree, Variant,
};

// --- PHASE 1: THE SCANNER ---
struct SymbolScanner {
    existing_symbols: HashSet<String>,
    defined_symbols: HashSet<String>,
}

impl<'ast> Visit<'ast> for SymbolScanner {
    fn visit_ident(&mut self, i: &'ast Ident) {
        self.existing_symbols.insert(i.to_string());
    }

    fn visit_pat_ident(&mut self, i: &'ast PatIdent) {
        self.defined_symbols.insert(i.ident.to_string());
        visit::visit_pat_ident(self, i);
    }

    fn visit_item_struct(&mut self, i: &'ast ItemStruct) {
        self.defined_symbols.insert(i.ident.to_string());
        visit::visit_item_struct(self, i);
    }

    fn visit_item_enum(&mut self, i: &'ast ItemEnum) {
        self.defined_symbols.insert(i.ident.to_string());
        visit::visit_item_enum(self, i);
    }

    fn visit_item_fn(&mut self, i: &'ast ItemFn) {
        if i.sig.ident != "main" {
            self.defined_symbols.insert(i.sig.ident.to_string());
        }
        visit::visit_item_fn(self, i);
    }

    fn visit_item_mod(&mut self, i: &'ast ItemMod) {
        self.defined_symbols.insert(i.ident.to_string());
        visit::visit_item_mod(self, i);
    }

    fn visit_item_trait(&mut self, i: &'ast ItemTrait) {
        self.defined_symbols.insert(i.ident.to_string());
        visit::visit_item_trait(self, i);
    }

    fn visit_variant(&mut self, v: &'ast Variant) {
        self.defined_symbols.insert(v.ident.to_string());
        visit::visit_variant(self, v);
    }

    fn visit_field(&mut self, f: &'ast Field) {
        if let Some(ident) = &f.ident {
            self.defined_symbols.insert(ident.to_string());
        }
        visit::visit_field(self, f);
    }
}

// --- PHASE 2: THE MINIFIER ---
struct RustMinifier {
    dictionary: HashMap<String, String>,
    reserved_symbols: HashSet<String>,
    defined_symbols: HashSet<String>,
    counter_lower: usize,
    counter_upper: usize,
}

impl RustMinifier {
    fn new(symbols: HashSet<String>, defined: HashSet<String>) -> Self {
        Self {
            dictionary: HashMap::new(),
            reserved_symbols: symbols,
            defined_symbols: defined,
            counter_lower: 0,
            counter_upper: 0,
        }
    }

    fn generate_short_name(&mut self, is_uppercase: bool) -> String {
        loop {
            let n = if is_uppercase {
                self.counter_upper
            } else {
                self.counter_lower
            };
            let base_char = if is_uppercase { b'A' } else { b'a' };

            let mut name = String::new();
            let mut temp_n = n;
            loop {
                name.push((base_char + (temp_n % 26) as u8) as char);
                temp_n /= 26;
                if temp_n == 0 {
                    break;
                }
            }

            if is_uppercase {
                self.counter_upper += 1;
            } else {
                self.counter_lower += 1;
            }

            if !self.is_protected_keyword(&name) && !self.reserved_symbols.contains(&name) {
                return name;
            }
        }
    }

    fn is_protected_keyword(&self, name: &str) -> bool {
        matches!(
            name,
            "as" | "break"
                | "const"
                | "continue"
                | "crate"
                | "else"
                | "enum"
                | "extern"
                | "false"
                | "fn"
                | "for"
                | "if"
                | "impl"
                | "in"
                | "let"
                | "loop"
                | "match"
                | "mod"
                | "move"
                | "mut"
                | "pub"
                | "ref"
                | "return"
                | "self"
                | "Self"
                | "static"
                | "struct"
                | "super"
                | "trait"
                | "true"
                | "type"
                | "unsafe"
                | "use"
                | "where"
                | "while"
                | "async"
                | "await"
                | "dyn"
                | "macro_rules"
                | "println"
                | "print"
                | "panic"
                | "vec"
                | "format"
                | "todo"
                | "String"
                | "Option"
                | "Result"
                | "i32"
                | "u32"
                | "f64"
                | "bool"
                | "str"
        )
    }

    fn register(&mut self, name: String) {
        if name == "main"
            || name.len() <= 1
            || self.is_protected_keyword(&name)
            || self.dictionary.contains_key(&name)
        {
            return;
        }
        let is_uppercase = name.chars().next().map_or(false, |c| c.is_uppercase());
        let short = self.generate_short_name(is_uppercase);
        self.dictionary.insert(name, short);
    }

    fn minify_token_stream(&self, tokens: TokenStream) -> TokenStream {
        tokens
            .into_iter()
            .map(|token| match token {
                TokenTree::Group(group) => {
                    let mut new_group = proc_macro2::Group::new(
                        group.delimiter(),
                        self.minify_token_stream(group.stream()),
                    );
                    new_group.set_span(group.span());
                    TokenTree::Group(new_group)
                }
                TokenTree::Ident(ident) => {
                    let name = ident.to_string();
                    if let Some(new_name) = self.dictionary.get(&name) {
                        TokenTree::Ident(Ident::new(new_name, ident.span()))
                    } else {
                        TokenTree::Ident(ident)
                    }
                }
                _ => token,
            })
            .collect()
    }

    fn use_tree_first_segment(tree: &UseTree) -> Option<String> {
        match tree {
            UseTree::Path(path) => Some(path.ident.to_string()),
            UseTree::Name(name) => Some(name.ident.to_string()),
            UseTree::Rename(rename) => Some(rename.ident.to_string()),
            UseTree::Group(group) => group
                .items
                .first()
                .and_then(|t| Self::use_tree_first_segment(t)),
            UseTree::Glob(_) => None,
        }
    }
}

impl VisitMut for RustMinifier {
    // Cette méthode gère maintenant TOUTES les déclarations de variables (let, mut, for, match, args)
    fn visit_pat_ident_mut(&mut self, i: &mut PatIdent) {
        let name = i.ident.to_string();
        self.register(name.clone());
        if let Some(new_name) = self.dictionary.get(&name) {
            i.ident = Ident::new(new_name, i.ident.span());
        }
        visit_mut::visit_pat_ident_mut(self, i);
    }

    // Gestion des usages de variables et appels de fonctions
    fn visit_ident_mut(&mut self, i: &mut Ident) {
        let name_str = i.to_string();
        if name_str != "main" {
            if let Some(new_name) = self.dictionary.get(&name_str) {
                *i = Ident::new(new_name, i.span());
            }
        }
    }

    fn visit_macro_mut(&mut self, i: &mut Macro) {
        if let Some(segment) = i.path.segments.last_mut() {
            let name = segment.ident.to_string();
            if !self.is_protected_keyword(&name) {
                if let Some(new_name) = self.dictionary.get(&name) {
                    segment.ident = Ident::new(new_name, segment.ident.span());
                }
            }
        }
        i.tokens = self.minify_token_stream(i.tokens.clone());
        visit_mut::visit_macro_mut(self, i);
    }

    fn visit_item_use_mut(&mut self, i: &mut ItemUse) {
        if let Some(first_seg) = Self::use_tree_first_segment(&i.tree) {
            let is_local = first_seg == "crate"
                || first_seg == "self"
                || first_seg == "super"
                || self.defined_symbols.contains(&first_seg);
            if !is_local {
                return;
            }
        } else {
            return;
        }
        visit_mut::visit_item_use_mut(self, i);
    }
}

pub fn bulk_refactoring(source_code: &str) -> String {
    let mut ast: File = syn::parse_str(source_code).expect("Parsing failed");

    // 1. SCAN
    let mut scanner = SymbolScanner {
        existing_symbols: HashSet::new(),
        defined_symbols: HashSet::new(),
    };
    visit::visit_file(&mut scanner, &ast);

    // 2. MINIFY
    let mut minifier = RustMinifier::new(
        scanner.existing_symbols.clone(),
        scanner.defined_symbols.clone(),
    );

    // Pré-enregistrement pour assurer la cohérence
    let mut sorted_defined: Vec<_> = scanner.defined_symbols.into_iter().collect();
    sorted_defined.sort();
    for name in sorted_defined {
        minifier.register(name);
    }

    minifier.visit_file_mut(&mut ast);

    // 3. OUTPUT
    quote!(#ast).to_string()
}
