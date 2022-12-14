
module Verification.Core.Computation.Unification.Monoidic.ToCoequalizer where

open import Verification.Conventions

open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Limit.Specific.Coequalizer
open import Verification.Core.Category.Std.Category.As.Monoid
open import Verification.Core.Setoid.Definition
open import Verification.Core.Set.Decidable
open import Verification.Core.Set.Discrete
open import Verification.Core.Data.Prop.Everything
open import Verification.Core.Data.Sum.Definition
open import Verification.Core.Order.Preorder
open import Verification.Core.Order.Lattice
open import Verification.Core.Computation.Unification.Definition
open import Verification.Core.Computation.Unification.Monoidic.PrincipalFamilyCat2
open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Core.Algebra.MonoidWithZero.Definition
open import Verification.Core.Algebra.MonoidWithZero.Ideal
open import Verification.Core.Algebra.MonoidAction.Definition


module _ {π : Category π} {{_ : isDiscrete β¨ π β©}} {{_ : isSet-Str β¨ π β©}} where
  module _ {a b : β¨ π β©} (f g : a βΆ b) where
    private
      f' g' : PathMon π
      f' = arrow f
      g' = arrow g
      -- J : Ideal-r β² PathMon π β²
      -- J = β²(CoeqSolutions f' g')β²
      All : Ideal-r β² PathMon π β²
      All = β² β€ β²
      II : Ideal-r β² PathMon π β²
      II = β²(CoeqSolutions f' g')β²

    module by-Principal-Unification {G : Submonoid β² PathMon π β²} (P : isPrincipal/βΊ-r G β²(CoeqSolutions f' g')β²) where
      proof : isDecidable (hasCoequalizer f g)
      proof = {!!}
      {-
      proof with split-+-Str (zeroOrCancel-r {{_:>_.Proof2> P}})
      ... | left (rep=[] , sndβ) = left (Ξ» X ->
              let rr = rep {{_:>_.Proof1> P}}
                  h : b βΆ β¨ X β©
                  h = Ο-Coeq
                  h' : PathMon π
                  h' = arrow h
                  Pβ : f' β h' βΌ g' β h'
                  Pβ = functoriality-arrow f h β»ΒΉ β incl (arrow βΌ-Coeq) β functoriality-arrow g h
                  Pβ : β¨ CoeqSolutions f' g' h' β©
                  Pβ = incl Pβ
                  Pβ : β¨ β¨ rr β·-Ide All β© h' β©
                  Pβ = β¨ β¨ principal-r β© β© Pβ
                  incl (x , xP , xQ) = Pβ

                  Pβ : h' βΌ rr β x
                  Pβ = xQ

                  Pβ : h' βΌ β
                  Pβ = Pβ β (rep=[] βββ refl)

                  Pβ : h' βΌ β -> π-π°
                  Pβ = Ξ» ()

              in Pβ Pβ
            )
      ... | just ((repββ , cancelRep) , Qβ) = case-PathMon (rep' β²(CoeqSolutions f' g')β²) of
        (Ξ» (p : rep' II βΌ [])  -> π-rec (repββ p))
        (Ξ» (p : rep' II βΌ idp) ->
          let Pβ : β¨ CoeqSolutions f' g' (rep' II) β©
              Pβ = Principal-r::rep-in-ideal

              Pβ : β¨ CoeqSolutions f' g' idp β©
              Pβ = transp-βΌ {{_}} {{isSubsetoid:CoeqSolutions}} p Pβ

              Pβ : arrow f β idp βΌ arrow g β idp
              Pβ = β¨ Pβ β©

              Pβ : arrow f βΌ arrow g
              Pβ = unit-r-β β»ΒΉ β Pβ β unit-r-β

              Pβ : f βΌ g
              Pβ = PathMon-arrow-path-inv f g refl refl β¨ Pβ β©

              X : Coeq-ExUniq f g b
              X = record
                    { Ο-CoeqEU = id
                    ; βΌ-CoeqEU = unit-r-β β Pβ β unit-r-β β»ΒΉ
                    ; elim-CoeqEU = Ξ» h _ -> h
                    ; reduce-CoeqEU = Ξ» _ _ -> unit-l-β
                    ; unique-CoeqEU = Ξ» i j p -> unit-l-β β»ΒΉ β p β unit-l-β
                    }

          in right (β² b β² {{by-CoeqEU-Coeq X}})
        )

        (Ξ» {b'} {c} {i} -> Ξ» {rep=i -> case-Decision (b β-Str b') of

          -- if b β  b', then there cannot exist a coequalizer
          (Ξ» (bβ’b' : b β’-Str b') ->

            -- We assume that we have a coeq
            left (Ξ» X ->
              let rr = rep {{_:>_.Proof1> P}}
                  h : b βΆ β¨ X β©
                  h = Ο-Coeq
                  h' : PathMon π
                  h' = arrow h
                  Pβ : f' β h' βΌ g' β h'
                  Pβ = functoriality-arrow f h β»ΒΉ β incl (arrow βΌ-Coeq) β functoriality-arrow g h
                  Pβ : β¨ CoeqSolutions f' g' h' β©
                  Pβ = incl Pβ
                  Pβ : β¨ β¨ rr β·-Ide All β© h' β©
                  Pβ = β¨ β¨ principal-r {{_:>_.Proof1> P}} β© β© Pβ
                  incl (x , xP , xQ) = Pβ

                  -- We derive that then an x must exist such that our coeq h' factors through rr (since rr is the representing element)
                  Pβ : h' βΌ rr β x
                  Pβ = xQ

                  Pβ : h' βΌ (arrow i) β x
                  Pβ = Pβ β (rep=i βββ refl)

                  -- We now look at the different cases for what x might be
                  Pβ = case-PathMon x of

                        (Ξ» (q : x βΌ []) ->
                          let Qβ : (h' βΌ []) -> _
                              Qβ = Ξ» {()}
                              Qβ : (arrow i β x βΌ [])
                              Qβ = (incl (arrow {π = π} refl) βββ q)
                          in Qβ (Pβ β Qβ))

                        (Ξ» (q : x βΌ idp) ->
                          let Qβ : (h' βΌ arrow i)
                              Qβ = Pβ β (incl (arrow {π = π} refl) βββ q) β unit-r-β
                              Qβ : h' βΌ (arrow i) -> b β‘-Str b'
                              Qβ = Ξ» {(incl (arrow _)) -> refl}
                          in π-rec (bβ’b' (Qβ Qβ))
                        )

                        (Ξ» {x0} {x1} {x'} (q : x βΌ arrow x') ->
                          case-Decision (c β-Str x0) of

                            -- if the composition i β x' is not well formed, i.e., cβ x0, then we have iβx' = []
                            (Ξ» {cβ’x0 ->
                              let Pβ : h' βΌ []
                                  Pβ = Pβ β (refl βββ q) β PathMon-non-matching-arrows cβ’x0 i x'
                                  Pβ : (h' βΌ []) -> _
                                  Pβ = Ξ» {()}
                              in Pβ Pβ
                            })

                            -- if the composition i β x' is well formed
                            (Ξ» {refl-StrId ->
                              let Pβ : h' βΌ (arrow (i β x'))
                                  Pβ = Pβ β (refl βββ q) β functoriality-arrow i x' β»ΒΉ
                                  Pβ : h' βΌ (arrow (i β x')) -> b β‘-Str b'
                                  Pβ = Ξ» {(incl (arrow _)) -> refl}
                              in π-rec (bβ’b' (Pβ Pβ))
                            })
                          )
              in Pβ
          ))

          -- finally, if b = b', we can show that i is a coequalizer
          (Ξ» {refl-StrId ->
            let Ο : b βΆ c
                Ο = i

                -- we know that rep is in the CoeqSolutions ideal
                Pβ : β¨ (CoeqSolutions f' g') (rep' II) β©
                Pβ = Principal-r::rep-in-ideal

                -- thus, since rep is actually the arrow i, it is also in this ideal
                Pβ : β¨ (CoeqSolutions f' g') (arrow i) β©
                Pβ = transp-βΌ rep=i Pβ

                -- by definition of this ideal, this means that fβi βΌ gβi
                Pβ : (arrow f β arrow i) βΌ (arrow g β arrow i)
                Pβ = β¨ Pβ β©

                -- we do know that the codomain of f/g and the domain of i match, thus, we can use functoriality of the arrow to
                -- get the same statement on the level of categories
                -- This finishes the proof that f β Ο βΌ g β Ο
                Pβ : f β i βΌ g β i
                Pβ =
                  let q : arrow {π = π} (f β i) βΌ arrow (g β i)
                      q = functoriality-arrow f i β Pβ β functoriality-arrow g i β»ΒΉ
                      q' : arrow {π = π} (f β i) βΌ arrow (g β i) -> f β i βΌ g β i
                      q' = Ξ» {(incl p) -> PathMon-arrow-path-inv (f β i) (g β i) refl refl p}
                      -- q' = Ξ» {(incl (arrow p)) -> p}
                  in q' q


                -- 2. We now have to show that given any other h which makes f and g equal, we get a hom from c.
                Pβ : β{d : β¨ π β©} -> (h : b βΆ d) -> (f β h βΌ g β h) -> (β Ξ» (j : c βΆ d) -> (i β j βΌ h))
                Pβ {d} h hP =
                  let h' = arrow h
                      rr = rep' II
                      -- we show that h is in the ideal
                      Qβ : β¨ CoeqSolutions f' g' h' β©
                      Qβ = incl (functoriality-arrow f h β»ΒΉ β incl (arrow hP) β functoriality-arrow g h)

                      -- this means that it is also element of the "factoring ideal"/principal ideal
                      Qβ : β¨ β¨ rr β·-Ide All β© h' β©
                      Qβ = β¨ β¨ principal-r {{_:>_.Proof1> P}} β© β© Qβ
                      incl (x , xP , xQ) = Qβ

                      -- i.e., we get
                      Qβ : h' βΌ rr β x
                      Qβ = xQ

                      Qβ : h' βΌ (arrow i) β x
                      Qβ = Qβ β (rep=i βββ refl)

                      -- we look at the different options for x
                      Qβ = case-PathMon x of

                          -- the case that x is [] can clearly not happen, for then the result of (arrow i β x) would not be an arrow
                          (Ξ» (q : x βΌ []) ->
                            let Rβ : (h' βΌ []) -> _
                                Rβ = Ξ» {()}
                                Rβ : (arrow i β x βΌ [])
                                Rβ = (incl (arrow {π = π} refl) βββ q)
                            in Rβ (Qβ β Rβ))

                          -- if x is idp, then h' is simply i
                          (Ξ» (q : x βΌ idp) ->
                            let Rβ : h' βΌ arrow i
                                Rβ = Qβ β (incl (arrow {π = π} refl) βββ q) β unit-r-β
                                Rβ : d β‘-Str c
                                Rβ = PathMon-arrow-path-matching-codom h i β¨ Rβ β©
                                Rβ : d β‘-Str c -> _
                                Rβ = Ξ» {refl-StrId ->
                                  let Rβ : h βΌ i
                                      Rβ = PathMon-arrow-path-inv h i refl refl β¨ Rβ β©
                                      Rβ : i β id βΌ h
                                      Rβ = unit-r-β β Rβ β»ΒΉ
                                  in id , Rβ
                                  }
                            in Rβ Rβ
                          )

                          -- the most interesting case is where x is really an arrow
                          (Ξ» {x0} {x1} {x'} (q : x βΌ arrow x') ->
                            -- but we still have to check whether the domain of x' fits to the codomain of Ο
                            case-Decision (c β-Str x0) of

                              -- if the composition i β x' is not well formed, i.e., cβ x0, then we have iβx' = []
                              (Ξ» {cβ’x0 ->
                                  let Pβ : h' βΌ []
                                      Pβ = Qβ β (refl βββ q) β PathMon-non-matching-arrows cβ’x0 i x'
                                      Pβ : (h' βΌ []) -> _
                                      Pβ = Ξ» {()}
                                  in Pβ Pβ
                              })

                              -- if the composition i β x' is well formed
                              (Ξ» {refl-StrId ->
                                -- and, further, we also have to check whether x1 = d
                                case-Decision (d β-Str x1) of

                                  -- the case that they are not equal cannot happen, since this would mean that Rβ shouldn't hold
                                  (Ξ» dβ’x1 ->
                                    let Rβ : h' βΌ (arrow (i β x'))
                                        Rβ = Qβ β (refl βββ q) β functoriality-arrow i x' β»ΒΉ
                                        Rβ : d β‘-Str x1
                                        Rβ = PathMon-arrow-path-matching-codom h (i β x') β¨ Rβ β©
                                    in π-rec (dβ’x1 Rβ)
                                  )

                                  -- if x1 = d
                                  (Ξ» {refl-StrId ->
                                    -- then we can return x'. But actually, we also want to show that the Ξ² rules hold for Ο, so we have to do...
                                    let -- we show the Ξ² rule
                                        Rβ : arrow (i β x') βΌ arrow h
                                        Rβ = functoriality-arrow i x' β (refl βββ q β»ΒΉ) β Qβ β»ΒΉ
                                        Rβ : (i β x') βΌ h
                                        Rβ = PathMon-arrow-path-inv (i β x') h refl refl β¨ Rβ β©

                                    in x' , Rβ
                                  })
                              }))
                  in Qβ

                -- the Ξ· rule, i.e., uniqueness of the coeq
                Pβ : β{d : β¨ π β©} -> (v w : c βΆ d) -> (i β v βΌ i β w) -> v βΌ w
                Pβ v w P =
                  let rr = rep' II
                      Qβ : rr β arrow v βΌ rr β arrow w
                      Qβ = (rep=i βββ refl) β functoriality-arrow i v β»ΒΉ β (incl (arrow P)) β functoriality-arrow i w β (rep=i β»ΒΉ βββ refl)
                      Qβ : arrow v βΌ arrow w
                      Qβ = cancelRep Qβ
                      Qβ : v βΌ w
                      Qβ = PathMon-arrow-path-inv v w refl refl β¨ Qβ β©
                  in Qβ


                -- we build the coequalizer structure
                X : Coeq-ExUniq f g c
                X = record
                      { Ο-CoeqEU = Ο
                      ; βΌ-CoeqEU = Pβ
                      ; elim-CoeqEU = Ξ» h p -> Pβ h p .fst
                      ; reduce-CoeqEU = Ξ» h p -> Pβ h p .snd
                      ; unique-CoeqEU = Pβ
                      }
            in right (β² c β² {{by-CoeqEU-Coeq X}})
          })
          })

-}



