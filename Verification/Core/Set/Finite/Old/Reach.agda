
module Verification.Core.Set.Finite.Old.Reach where

open import Verification.Conventions

open import Verification.Core.Setoid.Definition
open import Verification.Core.Set.Discrete
open import Verification.Core.Data.Prop.Everything
open import Verification.Core.Data.Universe.Definition
open import Verification.Core.Data.Universe.Instance.Category
open import Verification.Core.Order.Preorder
open import Verification.Core.Order.Lattice
open import Verification.Core.Order.HeytingAlgebra


-- π« : (A : π° π) -> π° (π βΊ)
-- π« {π} A = A -> Prop π

module _ {A : π° π} where
  β¦_β¦ : A -> A -> Prop π
  β¦ a β¦ b = β£ (a β‘-Str b) β£

  data Reachable : (p q : A -> Prop π) (_ : p β€ q) -> π° (π βΊ) where
    refl-Reach : β{p q : A -> Prop π} -> (s : p βΌ q) -> (s' : p β€ q) -> Reachable p q s'
    step-Reach : β{p q : A -> Prop π} -> β{a : A}
                 -> (pβ€q : p β€ q)
                 -> β¦ a β¦ β° p -> (Y : β¦ a β¦ β€ q)
                 -> (w : p β¨ β¦ a β¦ β€ q)
                 -> Reachable (p β¨ β¦ a β¦) q w
                 -> Reachable p q pβ€q

    transp-Reach : β{p q p' q'} -> (p βΌ p') -> (q βΌ q') -> {a : p β€ q} -> {b : p' β€ q'} -> Reachable p q a -> Reachable p' q' b

  comp-Reach : β{p q r : A -> Prop π} {X : p β€ q} {Y : q β€ r} -> Reachable p q X -> Reachable q r Y -> Reachable p r (X β‘ Y)
  comp-Reach (refl-Reach s s') q = refl-Reach {!!} {!!}
  comp-Reach (step-Reach _ x Y _ p) q = {!!} -- step-Reach ? x ? (comp-Reach p q)
  comp-Reach (transp-Reach x y p) = {!!}

module _ {A : π° π} {B : π° π} where
  Im : (A -> B) -> B -> Prop _
  Im f b = β£ (β Ξ» a -> f a β‘-Str b) β£

module _ {A B : π° π} {{_ : isDiscrete' B}} where

  private
    pb-Reach-impl : (f : A -> B) -> {p q : π« B} {{_ : isπ«-Dec p}} {p' q' : π« A} -> (p' β€ p β£ f) -> (q β£ f βΌ q')
                    -> {s : p' β€ q'} -> {t : (p β§ Im f) β€ (q β§ Im f)}
                    -> Reachable p' q' s -> Reachable (p β§ Im f) (q β§ Im f) t
    pb-Reach-impl f {p} {q} {p'} {q'} p'β€p qβΌq' {_} {t} (refl-Reach s (incl v)) = refl-Reach (antisym t (incl Pβ)) t --  (incl (β¨ t β© , Pβ)) t
      where
        Pβ : β {a} -> β¨ (q β§ Im f) a β© -> β¨ (p β§ Im f) a β©
        Pβ (qa , (b , refl-StrId)) =
          let -- X = {!!} -- β¨ (qβ€q' β‘ (incl (β¨ β¨ s {_} β»ΒΉ β© β©)) β‘ p'β€p) β© qa
              Y = β¨ p'β€p β© (β¨ β¨ (s β»ΒΉ) β© β© (β¨ β¨ qβΌq' β© β© qa))
          in Y , (b , refl-StrId)

    pb-Reach-impl f {p} {q} {{pdec}} {p'} {q'} p'β€p qβΌq' {_} {pfβ€qf} (step-Reach {a = a} (p'β€q') aβ°p' aβ€q' p'aβ€q' r) =
      let Pβ : (Β¬ β¨ p (f a) β©) β¨ β¨ p (f a) β©
          Pβ = decide-π« {P = p} (f a)

          Pβ : (p' β¨ β¦ a β¦) β€ (p β¨ β¦ f a β¦) β£ f
          Pβ = incl (Ξ» x β case x of
                            (Ξ» xβp' -> left (β¨ p'β€p β© xβp'))
                            (Ξ» xβa  -> right (cong-Str f xβa)))

          Rβ : β {i} -> (f a β‘-Str i) -> β¨ q i β©
          Rβ {i} = Ξ» {(refl-StrId) ->
              let Qβ : β¨ q' a β©
                  Qβ = β¨ aβ€q' β© refl

                  Qβ : β¨ q (f a) β©
                  Qβ = β¨ β¨ qβΌq' β»ΒΉ β© β© Qβ
              in Qβ}

          Pβ : (p β¨ β¦ f a β¦) β§ Im f β€ q β§ Im f
          Pβ = incl (Ξ» {i} -> Ξ» (x , y) β
              case x of
                (Ξ» iβp  -> let Qβ : β¨ (q β§ Im f) i β©
                               Qβ = β¨ pfβ€qf β© (iβp , y)
                           in (Qβ .fst) , Qβ .snd)
                (Ξ» fa=i -> Rβ fa=i , y))

          rβ = pb-Reach-impl f {p β¨ β¦ f a β¦} {q} {{it}} Pβ qβΌq' {_} {Pβ} r

          rβ = case Pβ of
            (Ξ» faβp ->
              let Pβ : β¦ f a β¦ β° p β§ Im f
                  Pβ faβ€pf = faβp (β¨ faβ€pf β© refl .fst)

                  Pβ : β¦ f a β¦ β€ q β§ Im f
                  Pβ = β¨ incl (Ξ» fa=i β Rβ fa=i) , (incl (Ξ» fa=i β _ , fa=i)) β©-β§

                  Pβ : p β§ Im f β¨ β¦ f a β¦ β€ q β§ Im f
                  Pβ = [ pfβ€qf , Pβ ]-β¨

                  Pβ : (p β¨ β¦ f a β¦) β§ Im f βΌ p β§ Im f β¨ β¦ f a β¦
                  Pβ = incl (Ξ» {i} ->
                      ((Ξ» (x , y) β case x of
                                          (Ξ» xβp -> left (xβp , y))
                                          (Ξ» fa=i -> right fa=i))
                      ,
                      (Ξ» x -> case x of
                                    (Ξ» (xβp , xβf) -> (left xβp , xβf))
                                    (Ξ» (fa=i)      -> (right fa=i , (_ , fa=i))))))

                  rβ = step-Reach pfβ€qf Pβ Pβ Pβ (transp-Reach Pβ refl rβ)
              in rβ)
            (Ξ» faβp ->
              let Pβ : p β¨ β¦ f a β¦ βΌ p
                  Pβ = antisym [ reflexive , incl (Ξ» {refl-StrId -> faβp}) ]-β¨ ΞΉβ-β¨
                  Pβ : (p β¨ β¦ f a β¦) β§ Im f βΌ p β§ Im f
                  Pβ = antisym (map-β§ (by-βΌ-β€ Pβ) reflexive) (map-β§ (by-βΌ-β€ Pβ β»ΒΉ ) reflexive)
              in transp-Reach Pβ refl rβ
              )
      in rβ

    pb-Reach-impl f {p} {q} {{pdec}} {p'} {q'} p'β€p qβΌq' (transp-Reach {p''} {q''} p''βΌp' q''βΌq' r) =
      let Pβ : p'' β€ p β£ f
          Pβ = (by-βΌ-β€ p''βΌp') β‘ p'β€p

          Pβ : q β£ f βΌ q''
          Pβ = qβΌq' β q''βΌq' β»ΒΉ

          rβ = pb-Reach-impl f {{pdec}} Pβ Pβ r
      in rβ

  rewrite-expre-π« : {f : A -> B} -> {p q : π« B} -> ((p β£ f) β€ (q β£ f)) -> (p β§ Im f) β€ (q β§ Im f)
  rewrite-expre-π« pfβ€qf = incl (Ξ» {i} -> Ξ» {(iβp , (_ , refl-StrId)) β β¨ pfβ€qf β© iβp , (_ , refl-StrId)})

  pb-Reach : (f : A -> B) -> (p q : π« B) {{_ : isπ«-Dec p}}
                  -> {s : (p β£ f) β€ (q β£ f)} -- -> {t : (p β§ Im f) β€ (q β§ Im f)}
                  -> Reachable (p β£ f) (q β£ f) s -> Reachable (p β§ Im f) (q β§ Im f) (rewrite-expre-π« s)
  pb-Reach f p q {s} r = pb-Reach-impl f reflexive refl r




