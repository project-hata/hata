
module Verification.Core.Data.Universe.Definition where

open import Verification.Core.Conventions

-- | - The identity morphisms [..] are given by [..].
id-π° : β{A : π° π} -> A -> A
id-π° a = a

macro
  idf : β{A : π° π} -> SomeStructure
  idf {A = A} = #structureOn (id-π° {A = A})

-- | - Let [..], [..] and [..] be types.
module _ {A : π° π} {B : π° π} {C : π° π} where
-- |> Then composition is given by:
  _β-π°_ : (f : A -> B) -> (g : B -> C) -> (A -> C)
  _β-π°_ f g a = g (f a)
  infixl 40 _β-π°_

  macro
    _β_ : (B -> C) [ πβ ]β (A -> B) [ πβ ]β SomeStructure
    _β_ = Ξ»str g β¦ Ξ»str f β¦ #structureOn (f β-π° g)
  infixl 40 _β_

macro
  ππ²π©π : β(π : π) -> SomeStructure
  ππ²π©π (π) = #structureOn (π°' π)

  ππ§π’π― : β(π : π) -> SomeStructure
  ππ§π’π― (π) = #structureOn (π°' π)

  ππ§π’π―β : SomeStructure
  ππ§π’π―β = #structureOn (π°β)

  ππ§π’π―β : SomeStructure
  ππ§π’π―β = #structureOn (π°β)


_β_ : β{π π} -> π° π -> π° π -> π° _
A β B = (A -> B) Γ-π° (B -> A)





-- mymap : β{A : ππ²π©π ββ} -> A -> A
-- mymap = {!!}

-- mymap2 : β{π : π} -> (ππ²π©π π) -> ππ²π©π π
-- mymap2 a = a


