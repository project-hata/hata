
module Verification.Core.Category.Std.Factorization.EpiMono.Variant.Split.Definition where

open import Verification.Conventions hiding (_โ_)

open import Verification.Core.Setoid.Definition
open import Verification.Core.Category.Std.AllOf.Collection.Basics
open import Verification.Core.Category.Std.AllOf.Collection.Limits
open import Verification.Core.Category.Std.Morphism.Epi.Definition


module _ {๐' : Category ๐} {{_ : hasCoproducts ๐'}} where
  private macro ๐ = #structureOn โจ ๐' โฉ

  record isSplitEpiMonoFactorizable {a b : ๐} (f : a โถ b) : ๐ฐ ๐ where
    constructor isSplitEpiMonoFactorizable:byDef
    field image : ๐
    field rest : ๐
    field splitting : image โ rest โ b
    field epiHom : a โถ image
    field {{isEpi:epiHom}} : isEpi epiHom
    field factors : f โ โจ splitting โฉโปยน โผ epiHom โ ฮนโ

  open isSplitEpiMonoFactorizable public

module _ (๐' : Category ๐) {{_ : hasCoproducts ๐'}} where

  private macro ๐ = #structureOn โจ ๐' โฉ

  record hasSplitEpiMonoFactorization : ๐ฐ ๐ where
    field factorize : โ{a b : ๐} -> (f : a โถ b) -> isSplitEpiMonoFactorizable f

  open hasSplitEpiMonoFactorization {{...}} public








