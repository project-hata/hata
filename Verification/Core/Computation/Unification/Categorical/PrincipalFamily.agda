
module Verification.Core.Computation.Unification.Categorical.PrincipalFamily where

open import Verification.Conventions
open import Verification.Core.Set.Induction.WellFounded
open import Verification.Core.Setoid
open import Verification.Core.Data.Universe.Definition
open import Verification.Core.Data.Universe.Instance.Category
open import Verification.Core.Order.Preorder
open import Verification.Core.Order.Lattice
open import Verification.Core.Order.WellFounded.Definition
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Category.As.ZeroMorphismCategory.Definition
open import Verification.Core.Category.Std.Category.Sized.Definition
open import Verification.Core.Computation.Unification.Categorical.Definition


record hasSizedFamily (๐ : ๐) (๐ : ZeroMorphismCategory ๐) : ๐ฐ (๐ โบ ๏ฝค ๐ โบ) where
  field Base : โจ ๐ โฉ -> ๐ฐ ๐
  field Ind : โจ ๐ โฉ -> ๐ฐ ๐
  field ๐ท : โ {a} -> Base a -> Ind a
  field ๐ : โ {a} -> (i : Ind a) -> Ideal a
  field Size : WFT (โโ , โโ)
  field size : โ{a} -> Ind a -> โจ Size โฉ

open hasSizedFamily {{...}} public

module _ (๐ : ๐ ^ 4) where
  CategoryWithSizedFamily : _
  CategoryWithSizedFamily = (ZeroMorphismCategory (๐ โ 0 โฏ 2)) :& hasSizedFamily (๐ โ 3)



module _ {๐ : ๐ ^ 3} {๐ : Category ๐} {{_ : isZeroMorphismCategory ๐}} {{_ : isSizedCategory ๐}} where

  module _ {{_ : hasSizedFamily ๐ โฒ โจ ๐ โฉ โฒ}} where
    record isSplittable {a : โจ ๐ โฉ} (n : โ) (i : Ind a) : ๐ฐ (๐ ๏ฝค ๐ โบ) where
      field fam : Fin-R n -> Ind a
      field covers : โ-fin (ฮป i -> ๐ (fam i)) โผ ๐ i
      field famprops : โ k -> size (fam k) โช size i
    open isSplittable public

record hasPrincipalFamily {๐ : ๐ ^ 3} {๐ : ๐} (๐ : Category ๐ :& (isSizedCategory :, (isZeroMorphismCategory :> hasSizedFamily ๐))) : ๐ฐ (๐ โบ ๏ฝค ๐) where
  field _โปยน*_ : โ{a b : โจ ๐ โฉ} (f : a โถ b) -> Ind a -> Ind b
  field size:โปยน* : โ{a b : โจ ๐ โฉ} (g : a โถ b) -> isGood g -> (i : Ind a) -> size (g โปยน* i) โชฃ size i
  field preserves-๐:โปยน* : โ{a b : โจ ๐ โฉ} {g : a โถ b} -> {i : Ind a} -> ๐ (g โปยน* i) โผ (g โปยนโท (๐ i))
  field principalBase : โ {a : โจ ๐ โฉ} -> โ (b : Base a) -> isEpiPrincipal (๐ (๐ท b))
  field โ : โ{a : โจ ๐ โฉ}(i : Ind a) -> (โ ฮป (b : Base a) -> ๐ (๐ท b) โผ ๐ i) +-๐ฐ (โ ฮป n -> isSplittable n i)

open hasPrincipalFamily {{...}} public

module _ (๐ : ๐ ^ 4) where
  CategoryWithPrincipalFamily : _
  CategoryWithPrincipalFamily = _ :& hasPrincipalFamily {๐ โ (0 โฏ 2)} {๐ โ 3}

module _ (๐ : ๐ฐ ๐)
  {{_ : isCategory {๐} ๐ }}
  {{_ : isSizedCategory โฒ ๐ โฒ}}
  {{_ : isZeroMorphismCategory โฒ ๐ โฒ}}
  {{_ : hasSizedFamily ๐ โฒ ๐ โฒ}}
  {{_ : hasPrincipalFamily โฒ ๐ โฒ}}
  -- {{_ : CategoryWithPrincipalFamily ๐ on ๐}} where
  where

  private
    P : (s : โจ Size โฉ) -> ๐ฐ _
    P s = โ{a : ๐} -> โ (i : Ind a) -> size i โก-Str s -> isEpiPrincipal (๐ i)

    lem-40 : โ{a : ๐} {U V : Ideal a}
              -> (PU : isEpiPrincipal U)
              -> isEpiPrincipal (repOf U {{PU}} โปยนโท V)
              -> isEpiPrincipal (V โง U)
    lem-40 {a} {U} {V} PU PV =
      let
          instance _ = PU
          instance _ = PV

          u : a โถ repObjOf U
          u = repOf U

          V' = u โปยนโท V

          v : repObjOf U โถ repObjOf V'
          v = repOf V'

          Pโ : (V โง U) โผ (u โ v) โท โค-Ideal
          Pโ = V โง U                                          โจ refl โโงโ principal-r โฉ-โผ
                (V โง (u โท โค-Ideal))                                 โจ inv-โท-r โปยน โฉ-โผ
                (u โท ((u โปยนโท V)))                              โจ refl โโทโ (principal-r)  โฉ-โผ
                (u โท ((v โท โค-Ideal)))                                โจ assoc-l-โท โปยน โฉ-โผ
                ((u โ v) โท โค-Ideal)                                   โ

      in record
         { repObj = _
         ; rep = u โ v
         ; principal-r = Pโ
         ; isGoodRep = isGood:โ isGoodRep isGoodRep
         ; zeroOrEpi = isZeroOrEpi:โ {๐' = โฒ ๐ โฒ} zeroOrEpi zeroOrEpi
         }


    lem-45 : โ{n} {a : ๐} -> (F : Fin-R n -> Ind a)
             -> (โ (i) -> โ{b} -> โ (g : a โถ b) -> isGood g -> isEpiPrincipal (๐ (g โปยน* F i)))
             -> isEpiPrincipal (โ-fin (ฮป j -> ๐ (F j)))
    lem-45 {zero} {a} F FP = isEpiPrincipal:โค
    lem-45 {suc n} {a} F FP =
        let
            instance
              Pโ : isEpiPrincipal (โ-fin (ฮป j -> ๐ (F (suc j))))
              Pโ = (lem-45 (ฮป j -> F (suc j)) (ฮป j -> FP (suc j)))

            r : a โถ _
            r = repOf (โ-fin (ฮป j -> ๐ (F (suc j)))) {{Pโ}}

            Pโ : isEpiPrincipal (๐ (r โปยน* F zero))
            Pโ = FP zero r (isGoodRep {{_}} {{Pโ}})

            Pโ : isEpiPrincipal (r โปยนโท ๐ (F zero))
            Pโ = transp-isEpiPrincipal preserves-๐:โปยน* Pโ
        in lem-40 Pโ Pโ

    lem-50 : โ s -> (โ t -> t โช s -> P t) -> P s
    lem-50 s IH {a} k refl-StrId with โ k
    ... | left (b , P) = let Pโ = principalBase b
                         in transp-isEpiPrincipal P Pโ
    ... | just (n , Split) =
      let Pโ : โ(i) -> โ{b : ๐} -> โ(g : a โถ b) -> isGood g -> isEpiPrincipal (๐ (g โปยน* Split .fam i))
          Pโ i g good = case size:โปยน* g good (fam Split i) of
                      (ฮป p ->
                        let Qโ : size (fam Split i) โช size k
                            Qโ = Split .famprops i
                            Qโ : size (g โปยน* fam Split i) โช size k
                            Qโ = transport-Str (cong-Str (ฮป ฮพ -> ฮพ โช size k) (sym-โฃ p)) Qโ
                        in IH (size (g โปยน* Split .fam i)) Qโ (g โปยน* fam Split i) refl-โฃ
                      )
                      (ฮป p ->
                        let Qโ : size (fam Split i) โช size k
                            Qโ = Split .famprops i
                            Qโ : size (g โปยน* fam Split i) โช size k
                            Qโ = p โก-โช Qโ
                        in IH (size (g โปยน* Split .fam i)) Qโ (g โปยน* fam Split i) refl-โฃ
                      )
          Pโ = lem-45 (Split .fam) Pโ
      in transp-isEpiPrincipal (Split .covers) Pโ

  isPrincipal:Family : โ s -> P s
  isPrincipal:Family = WFI.induction wellFounded lem-50

