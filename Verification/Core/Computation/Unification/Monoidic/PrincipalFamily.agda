
module Verification.Core.Computation.Unification.Monoidic.PrincipalFamily where

open import Verification.Conventions

open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Limit.Specific.Coequalizer
open import Verification.Core.Category.Std.Category.As.Monoid
open import Verification.Core.Setoid.Definition
open import Verification.Core.Setoid.Subsetoid
open import Verification.Core.Set.Decidable
open import Verification.Core.Set.Discrete
open import Verification.Core.Data.Prop.Everything
open import Verification.Core.Data.Sum.Definition
open import Verification.Core.Order.Preorder
open import Verification.Core.Order.Lattice
open import Verification.Core.Order.WellFounded.Definition
open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Core.Algebra.MonoidWithZero.Definition
open import Verification.Core.Algebra.MonoidWithZero.Ideal
open import Verification.Core.Algebra.MonoidAction.Definition
open import Verification.Core.Computation.Unification.Definition
-- open import Verification.Core.Theory.Presentation.Signature.Definition


module _ (M : Monoidβ (π , π)) where
  module _ (Good : Submonoid β² β¨ M β© β²) {B I : π° π} (π· : B -> I) (π : I -> Ideal-r M) where

    record isSplittable (n : β) (i : I) (P : I -> π°β) : π° (π ο½€ π βΊ) where
      field fam : Fin-R n -> I
      field covers : β-fin (Ξ» i -> π (fam i)) βΌ π i
      field famprops : β k -> P (fam k)
    open isSplittable public

    record isPrincipalFamily : π° (π ο½€ π βΊ) where
      field Size : WFT (ββ , ββ)
      -- field Size : π°β
      field size : I -> β¨ Size β©
      -- field _βͺ_ : Size -> Size -> π°β
      -- field isWellFounded:Size : WellFounded _βͺ_
      -- field trans-Size : β{a b c} -> a βͺ b -> b βͺ c -> a βͺ c
      field _β»ΒΉ*_ : β¦ β¨ Good β© β¦ -> I -> I
      field size:β»ΒΉ* : β g i -> (size (g β»ΒΉ* i) β‘-Str size i) +-π° (size (g β»ΒΉ* i) βͺ size i)
      field preserves-π:β»ΒΉ* : β {g i} -> π (g β»ΒΉ* i) βΌ (β¨ g β© β»ΒΉβ·-Ide (π i))
      -- field π : Idx -> Ideal-r M
      field β : (i : I) -> (β Ξ» b -> π (π· b) βΌ π i) +-π° (β Ξ» n -> isSplittable n i (Ξ» j -> size j βͺ size i))
      field principalBase : β b -> isPrincipal/βΊ-r Good (π (π· b))


  open isPrincipalFamily {{...}} public

  module _ (Good : Submonoid β² β¨ M β© β²) {B I : π° π} (π· : B -> I) (π : I -> Ideal-r M) {{PF : isPrincipalFamily Good π· π}} {{_ : zeroIsDecidable M}} where

    private
      P : (s : β¨ Size β©) -> π° _
      P s = β i -> size i β‘-Str s -> isPrincipal/βΊ-r Good (π i)

      lem-40 : β {U V : Ideal-r M} -> (PU : isPrincipal/βΊ-r Good U) -> isPrincipal/βΊ-r Good (rep' U β»ΒΉβ·-Ide V) -> isPrincipal/βΊ-r Good (V β§ U)
      lem-40 {U} {V} PU PV =
        let u : β¨ M β©
            u = rep' U

            V' = u β»ΒΉβ·-Ide V

            v : β¨ M β©
            v = rep' V'
            Pβ : (V β§ U) βΌ (u β v) β· β€
            Pβ = V β§ U                                          β¨ refl ββ§β (principal-r) β©-βΌ
                 V β§ (u β· β€)                                   β¨ refl ββ§β idem-β§ β»ΒΉ β©-βΌ
                 V β§ ((u β· β€) β§ (u β· β€))                      β¨ assoc-r-β§ β©-βΌ
                 (V β§ (u β· β€)) β§ (u β· β€)                      β¨ inv-β·Ide-r β»ΒΉ ββ§β refl β©-βΌ
                 (u β· (u β»ΒΉβ·-Ide V)) β§ (u β· β€)                 β¨ distr-β·-β§-Ide (zeroOrCancel-r {{_:>_.Proof2> PU}}) β»ΒΉ β©-βΌ
                 (u β· ((u β»ΒΉβ·-Ide V) β§ β€))                      β¨ refl ββ·β unit-r-β§ β©-βΌ
                 (u β· ((u β»ΒΉβ·-Ide V)))                           β¨ refl ββ·β (principal-r)  β©-βΌ
                 -- (u β· (v β· β€))                                   β¨ assoc-l-β· {A = Ideal-r β² β¨ M β© β² since isSetoid:Ideal-r} {m = u} {n = v} {a = β€} β»ΒΉ β©-βΌ
                 {-(u β· (v β· β€)) -} _                                 β¨ {!!} β©-βΌ
                 (u β v) β· (β€ since isIdeal-r:β€)   β
            instance
              Pβ : isPrincipal-r (V β§ U)
              Pβ = record { rep = u β v ; principal-r = Pβ }
            instance
              Pββ : isPrincipalβΊ-r Good β² β¨ V β§ U β© β²
              Pββ = record
                    { zeroOrCancel-r = (closed-β-ZeroOrCancel-r  (zeroOrCancel-r {{_:>_.Proof2> PU}}) (zeroOrCancel-r {{_:>_.Proof2> PV}}))
                    ; isGood = closed-β (isGood {{_:>_.Proof2> PU}}) (isGood {{_:>_.Proof2> PV}})
                    }
        in it

      lem-45 : β{n} -> (F : Fin-R n -> I) -> (β i -> β (g : β¦ β¨ Good β© β¦) -> isPrincipal/βΊ-r Good (π (g β»ΒΉ* F (i)))) -> isPrincipal/βΊ-r Good (β-fin (π β£ F))
      lem-45 {zero} F FP = it
      lem-45 {suc n} F FP =
        let
            Pβ : isPrincipal/βΊ-r Good (β-fin (π β£ (F β£ suc)))
            Pβ = (lem-45 (F β£ suc) (FP β£ suc))

            r : β¨ M β©
            r = rep' (β-fin (π β£ (F β£ suc))) {{_:>_.Proof1> Pβ}}

            rr : β¦ β¨ Good β© β¦
            rr = r β’ isGood {{_:>_.Proof2> Pβ}}

            Pβ : isPrincipal/βΊ-r Good (π (rr β»ΒΉ* F zero))
            Pβ = FP zero rr
            Pβ : isPrincipal/βΊ-r Good (β¨ rr β© β»ΒΉβ·-Ide π (F zero))
            Pβ = transp-isPrincipal/βΊ-r preserves-π:β»ΒΉ* Pβ
        in lem-40 Pβ Pβ

      lem-50 : β s -> (β t -> t βͺ s -> P t) -> P s
      lem-50 s IH k refl-StrId with β k
      ... | left (b , P) = let Pβ = principalBase b
                           in transp-isPrincipal/βΊ-r P Pβ
      ... | just (n , Split) =
        let Pβ : β i -> β(g : β¦ β¨ Good β© β¦) -> isPrincipal/βΊ-r Good (π (g β»ΒΉ* Split .fam i))
            Pβ i g = case size:β»ΒΉ* g (fam Split i) of
                       (Ξ» p ->
                          let Qβ : size (fam Split i) βͺ size k
                              Qβ = Split .famprops i
                              Qβ : size (g β»ΒΉ* fam Split i) βͺ size k
                              Qβ = transport-Str (cong-Str (Ξ» ΞΎ -> ΞΎ βͺ size k) (sym-β£ p)) Qβ
                          in IH (size (g β»ΒΉ* Split .fam i)) Qβ (g β»ΒΉ* fam Split i) refl-β£
                       )
                       (Ξ» p ->
                          let Qβ : size (fam Split i) βͺ size k
                              Qβ = Split .famprops i
                              Qβ : size (g β»ΒΉ* fam Split i) βͺ size k
                              Qβ = p β‘-βͺ Qβ
                          in IH (size (g β»ΒΉ* Split .fam i)) Qβ (g β»ΒΉ* fam Split i) refl-β£
                       )
            Pβ = lem-45 (Split .fam) Pβ
        in transp-isPrincipal/βΊ-r (Split .covers) Pβ


    isPrincipal:Family : β s -> P s
    isPrincipal:Family = WFI.induction wellFounded lem-50









