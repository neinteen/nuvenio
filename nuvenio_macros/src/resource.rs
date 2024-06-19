use proc_macro2::TokenStream;
use quote::quote;
use syn::{parse2, parse_quote, DeriveInput, Result};

pub(crate) fn derive_resource(input: TokenStream) -> Result<TokenStream> {
    let mut input = parse2::<DeriveInput>(input)?;

    input
        .generics
        .make_where_clause()
        .predicates
        .push(parse_quote!(Self: 'static));

    let name = &input.ident;
    let (impl_generics, ty_generics, where_clause) = input.generics.split_for_impl();

    Ok(quote! {
        #[automatically_derived]
        impl #impl_generics ::nuvenio::resource::Resource for #name #ty_generics #where_clause { }
    })
}
