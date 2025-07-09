use proc_macro::TokenStream;
use quote::quote;
use syn::{parse_macro_input, Data, DeriveInput, Fields};

#[proc_macro_attribute]
pub fn eterned(_attr: TokenStream, item: TokenStream) -> TokenStream {
    let input = parse_macro_input!(item as DeriveInput);

    let name = &input.ident;
    let visibility = &input.vis;

    // Extract the data field and its type
    let data_field = match &input.data {
        Data::Struct(data_struct) => match &data_struct.fields {
            Fields::Named(fields) => fields
                .named
                .iter()
                .find(|f| f.ident.as_ref().map(|i| i == "data").unwrap_or(false))
                .expect("eterned structs must have a 'data' field"),
            _ => panic!("eterned only supports structs with named fields"),
        },
        _ => panic!("eterned only supports structs"),
    };

    let data_type = &data_field.ty;

    // Find the return_ref attribute
    let return_ref_attr = data_field
        .attrs
        .iter()
        .find(|attr| attr.path().is_ident("return_ref"))
        .expect("data field must have #[return_ref(...)] attribute");

    let return_type = match return_ref_attr.parse_args::<syn::Type>() {
        Ok(ty) => ty,
        Err(_) => panic!("return_ref attribute must specify return type"),
    };

    let expanded = quote! {
        #[derive(Debug, Clone, PartialEq, Eq, Hash)]
        #visibility struct #name {
            pub data: #data_type,
        }

        impl #name {
            pub fn new<S: Into<String>>(s: S) -> Self {
                Self {
                    data: s.into(),
                }
            }

            pub fn as_str(&self) -> &#return_type {
                &self.data
            }
        }

        impl std::fmt::Display for #name {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                write!(f, "{}", self.data)
            }
        }

        impl From<String> for #name {
            fn from(s: String) -> Self {
                Self::new(s)
            }
        }

        impl From<&str> for #name {
            fn from(s: &str) -> Self {
                Self::new(s)
            }
        }

        impl AsRef<str> for #name {
            fn as_ref(&self) -> &str {
                &self.data
            }
        }
    };

    TokenStream::from(expanded)
}
