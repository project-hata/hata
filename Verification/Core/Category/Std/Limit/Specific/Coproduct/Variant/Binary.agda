
module Verification.Core.Category.Std.Limit.Specific.Coproduct.Variant.Binary where

open import Verification.Conventions hiding (_β_)
open import Verification.Core.Setoid.Definition
-- open import Verification.Core.Data.Fin.Definition
open import Verification.Core.Data.Product.Definition
open import Verification.Core.Data.Sum.Definition
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Morphism.Iso
open import Verification.Core.Category.Std.Category.Notation.Associativity

-- [Hide]
infixr 20 _[_]β2_
_[_]β2_ : β{π} (X : π° π) -> β (π : π ^ 2) -> (R : π° π) -> (π° _)
_[_]β2_ {π = π} X π R = {U : π° (π β 0)} -> (u : U) -> {{UU : hasU U (π) (π β 1)}} -> {{p : getU UU β‘-Str (X)}} -> R
-- _[_]β2_ {π = π} X π R = {U : π° (π β 0)} -> (u : UniverseHintWrapper U) -> {{UU : hasU U (π) (π β 1)}} -> {{p : getU UU β‘-Str (X)}} -> R

macro
  _Γ2_ : β{π π : π} {π π : π ^ 2} -> (π°' π) [ π ]β2 (π°' π) [ π ]β2 SomeStructure
  _Γ2_ = Ξ»str A β¦ Ξ»str B β¦ #structureOn (A Γ-π° B)
  infixr 40 _Γ2_

-- //

-- | Let [..] [] be a category.
module _ {π : π° π} {{_ : isCategory {π} π}} where

  -- |> The notion of initiality is related to "minimality"
  --    in a very obvious way.

  -- [Definition]
  -- | An object |x| of a category is called /initial/ if:
  record isInitial (x : π) : π° (π ο½€ π) where
    -- | It has an outgoing arrow to every object.
    field elim-β₯ : β{a} -> x βΆ a
    -- | These arrows are the only outgoing arrows.
    field expand-β₯ : β{a} -> {f : x βΆ a} -> f βΌ elim-β₯

  open isInitial {{...}} public
  -- //

  -- |> The notion of a coproduct is a bit more involved.

  -- [Definition]
  -- | We say that |x| is a coproduct of |a| and |b|,
  record isCoproduct (a b x : π) : π° (π ο½€ π) where
  -- | 1. If it is equipped with an inclusion from |a| and one from |b|.
    field ΞΉβ : a βΆ x
    field ΞΉβ : b βΆ x

    -- | 2. And given such structure on any object |c|, there is an arrow
    --      showing that |x| is more minimal.
    field β¦_β¦ : β{c} -> ((a βΆ c) Γ (b βΆ c)) -> x βΆ c
    -- | 3. Such that the following conditions hold.
    field reduce-ΞΉβ : β{c} {f : a βΆ c} {g : b βΆ c} -> ΞΉβ β β¦ f , g β¦ βΌ f
    field reduce-ΞΉβ : β{c} {f : a βΆ c} {g : b βΆ c} -> ΞΉβ β β¦ f , g β¦ βΌ g
    field expand-ΞΉβ,ΞΉβ  : β{c} {f : x βΆ c} -> f βΌ β¦ ΞΉβ β f , ΞΉβ β f β¦
    field {{isSetoidHom:β¦β¦}} : β{c} -> isSetoidHom β²((a βΆ c) Γ-π° (b βΆ c))β² (x βΆ c) (β¦_β¦ {c})
  -- //

  open isCoproduct {{...}} public
  {-# DISPLAY isCoproduct.ΞΉβ _ = ΞΉβ #-}
  {-# DISPLAY isCoproduct.ΞΉβ _ = ΞΉβ #-}
  {-# DISPLAY isCoproduct.β¦_β¦ _ x = β¦ x β¦ #-}


  -- [Hide]
  module _ {a b x y : π} (p : x β y) {{_ : isCoproduct a b x}} where

    private
      ΞΉβ' : a βΆ y
      ΞΉβ' = ΞΉβ β β¨ p β©

      ΞΉβ' : b βΆ y
      ΞΉβ' = ΞΉβ β β¨ p β©

      β¦_β¦' : β{z} -> β(p : ((a βΆ z) Γ (b βΆ z))) -> y βΆ z
      β¦_β¦' = Ξ» (f , g) β β¨ sym-β p β© β β¦ f , g β¦

      lem-1 : β{z} -> isSetoidHom β²((a βΆ z) Γ-π° (b βΆ z))β² (y βΆ z) β¦_β¦'
      lem-1 = record { cong-βΌ = Ξ» p β refl β cong-βΌ p}

      lem-2 : β{z} -> {f : (a βΆ z)} -> {g : (b βΆ z)} -> ΞΉβ' β β¦ f , g β¦' βΌ f
      lem-2 {f = f} {g} = (ΞΉβ β β¨ p β©) β (β¨ sym-β p β© β β¦ f , g β¦)   β¨ assoc-[ab][cd]βΌa[bc]d-β β©-βΌ
                          ΞΉβ β (β¨ p β© β β¨ sym-β p β©) β β¦ f , g β¦     β¨ refl β inv-r-β (of p) β refl β©-βΌ
                          ΞΉβ β id β β¦ f , g β¦                        β¨ unit-r-β β refl β©-βΌ
                          ΞΉβ β β¦ f , g β¦                             β¨ reduce-ΞΉβ β©-βΌ
                          f                                         β

    transp-β-Coproduct : isCoproduct a b y
    isCoproduct.ΞΉβ transp-β-Coproduct             = ΞΉβ'
    isCoproduct.ΞΉβ transp-β-Coproduct             = ΞΉβ'
    isCoproduct.β¦ transp-β-Coproduct β¦            = β¦_β¦'
    isCoproduct.isSetoidHom:β¦β¦ transp-β-Coproduct = lem-1
    isCoproduct.reduce-ΞΉβ transp-β-Coproduct      = lem-2
    isCoproduct.reduce-ΞΉβ transp-β-Coproduct      = {!!}
    isCoproduct.expand-ΞΉβ,ΞΉβ transp-β-Coproduct       = {!!}

  module _ {a b x y : π} {{_ : isCoproduct a b x}} {{_ : isCoproduct a b y}} where
    β:byIsCoproduct : x β y
    β:byIsCoproduct = f since P
      where
        f : x βΆ y
        f = β¦ ΞΉβ , ΞΉβ β¦

        g : y βΆ x
        g = β¦ ΞΉβ , ΞΉβ β¦

        lem-1 : f β g βΌ id
        lem-1 = f β g                           β¨ expand-ΞΉβ,ΞΉβ β©-βΌ
                β¦ ΞΉβ β (f β g) , ΞΉβ β (f β g) β¦ β¨ cong-βΌ (assoc-r-β , assoc-r-β) β©-βΌ
                β¦ (ΞΉβ β f) β g , (ΞΉβ β f) β g β¦ β¨ cong-βΌ (reduce-ΞΉβ β refl , reduce-ΞΉβ β refl) β©-βΌ
                β¦ ΞΉβ β g , ΞΉβ β g β¦             β¨ cong-βΌ (reduce-ΞΉβ , reduce-ΞΉβ) β©-βΌ
                β¦ ΞΉβ , ΞΉβ β¦                     β¨ cong-βΌ (unit-r-β β»ΒΉ , unit-r-β β»ΒΉ) β©-βΌ
                β¦ ΞΉβ β id , ΞΉβ β id β¦           β¨ expand-ΞΉβ,ΞΉβ β»ΒΉ β©-βΌ
                id                              β


        lem-2 : g β f βΌ id
        lem-2 = g β f                           β¨ expand-ΞΉβ,ΞΉβ β©-βΌ
                β¦ ΞΉβ β (g β f) , ΞΉβ β (g β f) β¦ β¨ cong-βΌ (assoc-r-β , assoc-r-β) β©-βΌ
                β¦ (ΞΉβ β g) β f , (ΞΉβ β g) β f β¦ β¨ cong-βΌ (reduce-ΞΉβ β refl , reduce-ΞΉβ β refl) β©-βΌ
                β¦ ΞΉβ β f , ΞΉβ β f β¦             β¨ cong-βΌ (reduce-ΞΉβ , reduce-ΞΉβ) β©-βΌ
                β¦ ΞΉβ , ΞΉβ β¦                     β¨ cong-βΌ (unit-r-β β»ΒΉ , unit-r-β β»ΒΉ) β©-βΌ
                β¦ ΞΉβ β id , ΞΉβ β id β¦           β¨ expand-ΞΉβ,ΞΉβ β»ΒΉ β©-βΌ
                id                              β

        P : isIso (hom f)
        P = record { inverse-β = g ; inv-r-β = lem-1 ; inv-l-β = lem-2 }

  module _ {a b : π} {{_ : isInitial a}} {{_ : isInitial b}} where
    β:byIsInitial : a β b
    β:byIsInitial = elim-β₯ since record
      { inverse-β = elim-β₯
      ; inv-r-β = expand-β₯ β expand-β₯ β»ΒΉ
      ; inv-l-β = expand-β₯ β expand-β₯ β»ΒΉ
      }



record hasInitial (π : Category π) : π° π where
  field β₯ : β¨ π β©
  field {{isInitial:β₯}} : isInitial β₯

open hasInitial {{...}} public

record hasCoproducts (π : Category π) : π° π where
  infixl 80 _β_
  field _β_ : β¨ π β© -> β¨ π β© -> β¨ π β©
  field {{isCoproduct:β}} : β{a b} -> isCoproduct a b (a β b)

open hasCoproducts {{...}} public
{-# DISPLAY hasCoproducts._β_ _ x y = x β y #-}

record hasFiniteCoproducts (π : Category π) : π° π where
  field {{hasInitial:this}} : hasInitial π
  field {{hasCoproducts:this}}    : hasCoproducts π

open hasFiniteCoproducts {{...}} public

module _ {π : Category π} {{_ : hasCoproducts π}} {{_ : hasInitial π}} where
  hasFiniteCoproducts:default : hasFiniteCoproducts π
  hasFiniteCoproducts.hasInitial:this hasFiniteCoproducts:default  = it
  hasFiniteCoproducts.hasCoproducts:this hasFiniteCoproducts:default     = it


module _ {π : Category π} {{_ : hasFiniteCoproducts π}} where
  macro
    ββ¨ : SomeStructure
    ββ¨ = #structureOn (Ξ»β _β_)

module _ {πα΅ : π° π} {{_ : isCategory {π} πα΅}} {{_ : hasCoproducts β² πα΅ β² }} where

  private macro π = #structureOn πα΅
  private instance _ = isSetoidHom:β¦β¦

  β¦β_ββ¦ : β{a b c : π} {fβ fβ : a βΆ c} {gβ gβ : b βΆ c} -> (fβ βΌ fβ) Γ (gβ βΌ gβ) -> β¦ fβ , gβ β¦ βΌ β¦ fβ , gβ β¦
  β¦β_ββ¦ = cong-βΌ

  append-β¦β¦ : β{a b c d : π} {f : a βΆ c} {g : b βΆ c} {h : c βΆ d}
            -> β¦ f , g β¦ β h βΌ β¦ f β h , g β h β¦
  append-β¦β¦ {f = f} {g} {h} =
    β¦ f , g β¦ β h                                     β¨ expand-ΞΉβ,ΞΉβ β©-βΌ
    β¦ ΞΉβ β (β¦ f , g β¦ β h) , ΞΉβ β (β¦ f , g β¦ β h) β¦   β¨ β¦β (assoc-r-β β (reduce-ΞΉβ β refl))
                                                        , (assoc-r-β β (reduce-ΞΉβ β refl)) ββ¦ β©-βΌ
    β¦ f β h , g β h β¦                                 β

-- //


