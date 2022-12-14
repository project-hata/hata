
module Verification.Core.Category.Std.Functor.RelativeAdjoint where

open import Verification.Conventions

open import Verification.Core.Setoid.Definition
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Category.Instance.Category
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Category.Std.Natural.Definition
open import Verification.Core.Category.Std.Category.Notation.Associativity



module _ {š : Category š} {š : Category š} {ā° : Category š} where

  record isRelativeAdjoint (J : Functor š ā°) (F : Functor š š) (G : Functor š ā°) : š° (š ļ½¤ š ļ½¤ š) where
    field refree : ā{a : āØ š ā©} {b : āØ š ā©} -> āØ J ā© a ā¶ āØ G ā© b -> āØ F ā© a ā¶ b
    field recofree : ā{a : āØ š ā©} {b : āØ š ā©} -> āØ F ā© a ā¶ b -> āØ J ā© a ā¶ āØ G ā© b


--     field adj    : ā{a : āØ š ā©} -> āØ F ā© (āØ G ā© a) ā¶ a
--     field coadj  : ā{a : āØ š ā©} -> a ā¶ āØ G ā© (āØ F ā© a)
--     field {{isNatural:adj}} : isNatural (G ā-ššš­ F) id adj
--     field {{isNatural:coadj}} : isNatural id (F ā-ššš­ G) coadj
--     field reduce-coadj : ā{b : āØ š ā©}  -> coadj ā map adj ā¼ id {a = āØ G ā© b}
--     field reduce-adj : ā{a : āØ š ā©}    -> map coadj ā adj ā¼ id {a = āØ F ā© a}

  open isRelativeAdjoint {{...}} public


  module _ {J : Functor š ā°} {F : Functor š š} {G : Functor š ā°} {{_ : isRelativeAdjoint J F G}} where

    module _ {a : āØ š ā©} {b c : āØ š ā©} where
      module _ {fā fā : āØ J ā© a ā¶ āØ G ā© b} {gā gā : b ā¶ c} where
        destruct-precomp-free : (refree fā ā gā ā¼ refree fā ā gā) -> fā ā map gā ā¼ fā ā map gā
        destruct-precomp-free p = {!!}

        construct-precomp-free : fā ā map gā ā¼ fā ā map gā -> (refree fā ā gā ā¼ refree fā ā gā)
        construct-precomp-free = {!!}
        -- pā
--           where
--             pā = p
--                  >> free f ā g ā¼ free f ā h <<

--                  āŖ cong-ā¼ ā«

--                  -- >> map (free f ā g) ā¼ map (free f ā h) <<

--                  āŖ functoriality-ā āā¼ā functoriality-ā ā«

--                  -- >> map (free f) ā map g ā¼ map (free f) ā map h <<

--                  -- >> map (map f ā adj) ā map g ā¼ map (map f ā adj) ā map h <<

--                  āŖ functoriality-ā ā refl āā¼ā
--                    functoriality-ā ā refl ā«

--                  -- >> map (map f) ā map adj ā map g ā¼ map (map f) ā map adj ā map h <<

--                  āŖ refl ā_ ā«

--                  -- >> coadj ā (map (map f) ā map adj ā map g) ā¼ coadj ā (map (map f) ā map adj ā map h) <<

--                  āŖ assoc-[abcd]ā¼a[bcd]-ā ā»Ā¹ āā¼ā
--                    assoc-[abcd]ā¼a[bcd]-ā ā»Ā¹ ā«

--                  -- >> coadj ā map (map f) ā map adj ā map g ā¼ coadj ā map (map f) ā map adj ā map h <<

--                  āŖ naturality f ā refl ā refl āā¼ā
--                    naturality f ā refl ā refl ā«

--                  -- >> f ā coadj ā map adj ā map g ā¼ f ā coadj ā map adj ā map h <<

--                  āŖ assoc-[abcd]ā¼a[bc]d-ā āā¼ā
--                    assoc-[abcd]ā¼a[bc]d-ā ā«

--                  -- >> f ā (coadj ā map adj) ā map g ā¼ f ā (coadj ā map adj) ā map h <<

--                  āŖ refl ā reduce-coadj ā refl āā¼ā
--                    refl ā reduce-coadj ā refl ā«

--                  -- >> f ā id ā map g ā¼ f ā id ā map h <<

--                  āŖ unit-r-ā ā refl āā¼ā
--                    unit-r-ā ā refl ā«

--                  >> f ā map g ā¼ f ā map h <<






