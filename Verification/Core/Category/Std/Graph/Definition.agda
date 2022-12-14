
module Verification.Core.Category.Std.Graph.Definition where

open import Verification.Core.Conventions

open import Verification.Core.Setoid

open import Verification.Conventions.Meta.Term

record isGraph {π π} (A : π° π) : π° (π ο½€ (π βΊ)) where
  constructor graph
  field Edge : A -> A -> π° π

open isGraph {{...}} public

Graph : β (π : π ^ 2) -> π° _
Graph π = π° (π β 0) :& isGraph {π β 1}


record GraphSetoid (G : Graph π) : π° (π β 0) where
  constructor incl
  field β¨_β© : β¨ G β©

open GraphSetoid public

data RST (G : Graph π) : (a b : GraphSetoid G) -> π° π where
  incl : β{a b} -> Edge β¨ a β© β¨ b β© -> RST G a b
  refl-RST : β{a} -> RST G a a
  sym-RST : β{a b} -> RST G a b -> RST G b a
  trans-RST : β{a b c} -> RST G a b -> RST G b c -> RST G a c

instance
  isSetoid:RST : β{G : Graph π} -> isSetoid (GraphSetoid G)
  isSetoid:RST {G = G} = isSetoid:byDef (RST G) (refl-RST) sym-RST trans-RST


GraphβSetoid : Graph π -> Setoid _
GraphβSetoid G = GraphSetoid G since it

instance Register:GraphβSetoid = registerβ[ "" , π ] GraphβSetoid {π}


private macro
  F'''' = instance[ "" , π ] (Graph π -> Setoid _) β





