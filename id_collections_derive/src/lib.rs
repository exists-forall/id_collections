use proc_macro2::{Span, TokenStream};
use proc_macro_crate::{crate_name, FoundCrate};
use quote::{quote, quote_spanned};
use syn::{
    parse_macro_input, spanned::Spanned, Attribute, AttributeArgs, Data, DataStruct, DeriveInput,
    Error, Fields, Ident, Lit, Meta, NestedMeta,
};

fn parse_struct_input(input: &DeriveInput) -> Result<&DataStruct, Error> {
    if !input.generics.params.is_empty() {
        return Err(Error::new_spanned(
            &input.generics,
            "cannot derive Id for type with generic parameters",
        ));
    }

    let struct_def = match &input.data {
        Data::Struct(struct_def) => struct_def,
        Data::Enum(enum_def) => {
            return Err(Error::new_spanned(
                enum_def.enum_token,
                "the Id trait can only be derived for structs",
            ));
        }
        Data::Union(union_def) => {
            return Err(Error::new_spanned(
                union_def.union_token,
                "the Id trait can only be derived for structs",
            ));
        }
    };

    if struct_def.fields.is_empty() {
        return Err(Error::new_spanned(
            &struct_def.fields,
            "cannot derive Id trait for struct with no fields",
        ));
    } else if struct_def.fields.len() > 1 {
        return Err(Error::new_spanned(
            &struct_def.fields,
            "cannot derive Id trait for struct with more than one field",
        ));
    }

    Ok(struct_def)
}

fn get_crate_path(orig_name: &str) -> TokenStream {
    match crate_name(orig_name) {
        Ok(FoundCrate::Itself) => quote!(crate),
        Ok(FoundCrate::Name(name)) => {
            let ident = Ident::new(&name, Span::call_site());
            quote!(::#ident)
        }
        Err(_) => {
            // Fallback; default to using original name
            let ident = Ident::new(orig_name, Span::call_site());
            quote!(::#ident)
        }
    }
}

// The 'is_doctest_...' attribute allows us to work around a limitation of the 'proc_macro_crate'
// library which prevents it from working correctly in doctests. See
// https://github.com/bkchr/proc-macro-crate/issues/14
//
// We append a uuid to this internal attribute to avoid name collisions with other crates.
fn is_doctest(attrs: &[Attribute]) -> bool {
    let is_doctest_ident = Ident::new(
        "is_doctest_b244a423_69a4_4e0c_9697_283f66a8ba88",
        Span::call_site(),
    );
    attrs
        .iter()
        .any(|attr| attr.path.is_ident(&is_doctest_ident))
}

#[proc_macro_derive(Id, attributes(is_doctest_b244a423_69a4_4e0c_9697_283f66a8ba88))]
pub fn derive_id(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let input = parse_macro_input!(input as DeriveInput);

    let struct_def = match parse_struct_input(&input) {
        Ok(struct_def) => struct_def,
        Err(err) => return err.into_compile_error().into(),
    };

    let struct_name = &input.ident;

    let id_collections_path = if is_doctest(&input.attrs) {
        quote!(::id_collections)
    } else {
        get_crate_path("id_collections")
    };
    let trait_name = quote!(#id_collections_path::Id);

    match &struct_def.fields {
        Fields::Named(fields_named) => {
            assert_eq!(fields_named.named.len(), 1);
            let field = fields_named.named.first().unwrap();
            let field_name = field.ident.as_ref().unwrap();
            let field_type = &field.ty;
            quote_spanned! {
                field_type.span() =>
                impl #trait_name for #struct_name {
                    type Index = #field_type;

                    #[inline]
                    fn from_index(index: Self::Index) -> Self {
                        #struct_name { #field_name: index }
                    }

                    #[inline]
                    fn to_index(self) -> Self::Index {
                        self.#field_name
                    }
                }
            }
            .into()
        }
        Fields::Unnamed(fields_unnamed) => {
            assert_eq!(fields_unnamed.unnamed.len(), 1);
            let field = fields_unnamed.unnamed.first().unwrap();
            let field_type = &field.ty;
            quote_spanned! {
                field_type.span() =>
                impl #trait_name for #struct_name {
                    type Index = #field_type;

                    #[inline]
                    fn from_index(index: Self::Index) -> Self {
                        #struct_name(index)
                    }

                    #[inline]
                    fn to_index(self) -> Self::Index {
                        self.0
                    }
                }
            }
            .into()
        }
        Fields::Unit => unreachable!(),
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum DebugOpt {
    False,
    Standard,
    Compact,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum SerdeOpt {
    False,
    True,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Opts {
    debug_opt: DebugOpt,
    serde_opt: SerdeOpt,
}

fn parse_id_type_opts(attr_args: &AttributeArgs) -> Result<Opts, Span> {
    let mut debug_opt = None;
    let mut serde_opt = None;

    for arg in attr_args {
        match arg {
            NestedMeta::Meta(Meta::NameValue(name_value)) => {
                if name_value.path.leading_colon.is_some() || name_value.path.segments.len() != 1 {
                    return Err(name_value.path.span());
                }
                let segment = name_value.path.segments.last().unwrap();
                if !segment.arguments.is_empty() {
                    return Err(segment.arguments.span());
                }
                let key = segment.ident.to_string();
                let value = &name_value.lit;
                match key.as_str() {
                    "debug" => {
                        if debug_opt.is_some() {
                            return Err(segment.ident.span());
                        }
                        let new_opt = match value {
                            Lit::Bool(lit_bool) if !lit_bool.value => DebugOpt::False,
                            Lit::Str(lit_str) => match lit_str.value().as_str() {
                                "standard" => DebugOpt::Standard,
                                "compact" => DebugOpt::Compact,
                                _ => return Err(lit_str.span()),
                            },
                            _ => return Err(value.span()),
                        };
                        debug_opt = Some(new_opt);
                    }
                    "serde" => {
                        if serde_opt.is_some() {
                            return Err(segment.ident.span());
                        }
                        let new_opt = match value {
                            Lit::Bool(lit_bool) => {
                                if lit_bool.value {
                                    SerdeOpt::True
                                } else {
                                    SerdeOpt::False
                                }
                            }
                            _ => return Err(value.span()),
                        };
                        serde_opt = Some(new_opt);
                    }
                    _ => return Err(segment.ident.span()),
                }
            }
            _ => return Err(arg.span()),
        }
    }

    Ok(Opts {
        debug_opt: debug_opt.unwrap_or(DebugOpt::Compact),
        serde_opt: serde_opt.unwrap_or(SerdeOpt::False),
    })
}

#[proc_macro_attribute]
pub fn id_type(
    attr_args_tokens: proc_macro::TokenStream,
    input: proc_macro::TokenStream,
) -> proc_macro::TokenStream {
    let attr_args = parse_macro_input!(attr_args_tokens as AttributeArgs);

    let opts = match parse_id_type_opts(&attr_args) {
        Ok(opts) => opts,
        Err(span) => {
            return Error::new(span, "unexpected argument in 'id_type' macro")
                .into_compile_error()
                .into()
        }
    };

    let input = parse_macro_input!(input as DeriveInput);

    let struct_def = match parse_struct_input(&input) {
        Ok(struct_def) => struct_def,
        Err(err) => return err.into_compile_error().into(),
    };

    let derive_debug = match opts.debug_opt {
        DebugOpt::False | DebugOpt::Compact => {
            quote!()
        }
        DebugOpt::Standard => quote!(Debug,),
    };

    let derive_serde = match opts.serde_opt {
        SerdeOpt::False => {
            quote!()
        }
        SerdeOpt::True => {
            let serde_path = get_crate_path("serde");
            quote!(#serde_path::Serialize, #serde_path::Deserialize)
        }
    };

    let id_collections_path = if is_doctest(&input.attrs) {
        quote!(::id_collections)
    } else {
        get_crate_path("id_collections")
    };

    let derives = quote!(#[derive(
        Clone,
        Copy,
        PartialEq,
        Eq,
        PartialOrd,
        Ord,
        Hash,
        #id_collections_path::Id,
        #derive_debug
        #derive_serde
    )]);

    let compact_debug = match opts.debug_opt {
        DebugOpt::False | DebugOpt::Standard => quote!(),
        DebugOpt::Compact => {
            let struct_name = &input.ident;
            let struct_name_string = struct_name.to_string();
            match &struct_def.fields {
                Fields::Named(fields_named) => {
                    assert_eq!(fields_named.named.len(), 1);
                    let field = fields_named.named.first().unwrap();
                    let field_name = field.ident.as_ref().unwrap();
                    let field_name_string = field_name.to_string();
                    quote! {
                        impl ::std::fmt::Debug for #struct_name {
                            fn fmt(&self, f: &mut ::std::fmt::Formatter<'_>) -> ::std::fmt::Result {
                                write!(
                                    f,
                                    "{} {{ {}: {} }}",
                                    #struct_name_string,
                                    #field_name_string,
                                    self.#field_name,
                                )
                            }
                        }
                    }
                }
                Fields::Unnamed(fields_unnamed) => {
                    assert_eq!(fields_unnamed.unnamed.len(), 1);
                    quote! {
                        impl ::std::fmt::Debug for #struct_name {
                            fn fmt(&self, f: &mut ::std::fmt::Formatter<'_>) -> ::std::fmt::Result {
                                write!(
                                    f,
                                    "{}({})",
                                    #struct_name_string,
                                    self.0,
                                )
                            }
                        }
                    }
                }
                Fields::Unit => unreachable!(),
            }
        }
    };

    quote! {
        #derives
        #input
        #compact_debug
    }
    .into()
}
