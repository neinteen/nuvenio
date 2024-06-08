use proc_macro2::{Ident, Span, TokenStream};
use quote::quote;
use syn::{parse2, parse_quote, Data, DeriveInput, Error, GenericParam, LitInt, Result, Type};

use crate::util::{make_tuple, replace_lifetime};

pub(crate) fn derive_handler_param(input: TokenStream) -> Result<TokenStream> {
    let mut input = parse2::<DeriveInput>(input)?;
    let name = &input.ident;

    let lifetimes;
    let tuple_ty;
    let get_body;

    match &input.data {
        Data::Struct(struct_) => {
            lifetimes = input
                .generics
                .params
                .iter()
                .filter_map(|p| match p {
                    GenericParam::Lifetime(life) => Some(life.clone()),
                    GenericParam::Type(_) => None,
                    GenericParam::Const(_) => None,
                })
                .collect::<Vec<_>>();

            tuple_ty = make_tuple(struct_.fields.iter().map(|f| &f.ty));

            let where_clause = input.generics.make_where_clause();

            for field in &struct_.fields {
                let ty = &field.ty;

                let mut replaced_ty = ty.clone();

                for life in &lifetimes {
                    replace_lifetime(&mut replaced_ty, &life.lifetime.ident, &parse_quote!(__a));
                }

                where_clause.predicates.push(
                    parse_quote!(#ty: for<'__a> ::nuvenio::handler::HandlerParam<This<'__a> = #replaced_ty>),
                );
            }

            get_body = match &struct_.fields {
                syn::Fields::Named(fields) => {
                    let idents: Vec<_> = fields
                        .named
                        .iter()
                        .map(|f| f.ident.clone().unwrap())
                        .collect();

                    let underscored_idents: Vec<_> = idents
                        .iter()
                        .map(|i| Ident::new(&format!("__{i}"), Span::call_site()))
                        .collect();

                    quote! {
                        let (#(#underscored_idents,)*) = <#tuple_ty as ::nuvenio::handler::HandlerParam>::get(
                            state,
                            info,
                            event_ptr,
                            target_location,
                            world
                        );

                        #name {
                            #(#idents: #underscored_idents),*
                        }
                    }
                }
                syn::Fields::Unnamed(fields) => {
                    let indices = fields
                        .unnamed
                        .iter()
                        .enumerate()
                        .map(|(i, _)| LitInt::new(&format!("{i}"), Span::call_site()));

                    quote! {
                        let __tuple = <#tuple_ty as ::nuvenio::handler::HandlerParam>::get(
                            state,
                            info,
                            event_ptr,
                            target_location,
                            world
                        );

                        #name(#(__tuple.#indices),*)
                    }
                }
                syn::Fields::Unit => quote!(#name),
            };
        }
        Data::Enum(_) => {
            return Err(Error::new(
                Span::call_site(),
                "cannot derive `HandlerParam` on enums",
            ))
        }
        Data::Union(_) => {
            return Err(Error::new(
                Span::call_site(),
                "cannot derive `HandlerParam` on unions",
            ))
        }
    }

    let (impl_generics, ty_generics, where_clause) = input.generics.split_for_impl();

    let mut this: Type = parse_quote!(#name #ty_generics);
    for life in &lifetimes {
        replace_lifetime(&mut this, &life.lifetime.ident, &parse_quote!(__a));
    }

    Ok(quote! {
        #[automatically_derived]
        unsafe impl #impl_generics ::nuvenio::handler::HandlerParam for #name #ty_generics #where_clause {
            type State = <#tuple_ty as ::nuvenio::handler::HandlerParam>::State;

            type This<'__a> = #this;

            fn init(
                world: &mut ::nuvenio::world::World,
                config: &mut ::nuvenio::handler::HandlerConfig,
            ) -> ::core::result::Result<Self::State, ::nuvenio::handler::InitError>
            {
                <#tuple_ty as ::nuvenio::handler::HandlerParam>::init(world, config)
            }

            unsafe fn get<'__a>(
                state: &'__a mut Self::State,
                info: &'__a ::nuvenio::handler::HandlerInfo,
                event_ptr: ::nuvenio::event::EventPtr<'__a>,
                target_location: ::nuvenio::entity::EntityLocation,
                world: ::nuvenio::world::UnsafeWorldCell<'__a>,
            ) -> Self::This<'__a> {
                #get_body
            }

            fn refresh_archetype(
                state: &mut Self::State,
                arch: &::nuvenio::archetype::Archetype
            ) {
                <#tuple_ty as ::nuvenio::handler::HandlerParam>::refresh_archetype(
                    state,
                    arch
                )
            }

            fn remove_archetype(
                state: &mut Self::State,
                arch: &::nuvenio::archetype::Archetype
            ) {
                <#tuple_ty as ::nuvenio::handler::HandlerParam>::remove_archetype(
                    state,
                    arch
                )
            }
        }
    })
}
