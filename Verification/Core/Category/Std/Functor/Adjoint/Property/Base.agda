
module Verification.Core.Category.Std.Functor.Adjoint.Property.Base where

open import Verification.Conventions

open import Verification.Core.Setoid.Definition
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Category.Instance.Category
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Category.Std.Natural.Definition
open import Verification.Core.Category.Std.Category.Notation.Associativity

open import Verification.Core.Category.Std.Functor.Adjoint.Definition

module _ {š : Category š} {š : Category š} where

  module _ {F : Functor š š} {G : Functor š š} {{_ : F ā£ G}} where
    module _ {a b : āØ š ā©} {c : āØ š ā©} where
      module _ {f g : a ā¶ b} {h i : āØ F ā© b ā¶ c} where
        construct-postcomp-cofree : map f ā h ā¼ map g ā i -> f ā cofree h ā¼ g ā cofree i
        construct-postcomp-cofree p = p
                 >> map f ā h ā¼ map g ā i <<
                 āŖ cong-ā¼ ā«
                 >> map (map f ā h) ā¼ map (map g ā i) <<
                 āŖ functoriality-ā āā¼ā functoriality-ā ā«
                 >> map (map f) ā map h ā¼ map (map g) ā map i <<
                 āŖ (refl ā_) ā«
                 >> coadj _ ā (map (map f) ā map h) ā¼ coadj _ ā (map (map g) ā map i) <<
                 āŖ assoc-r-ā āā¼ā assoc-r-ā ā«
                 >> (coadj _ ā map (map f)) ā map h ā¼ (coadj _ ā map (map g)) ā map i <<
                 āŖ naturality f ā refl āā¼ā naturality g ā refl ā«
                 >> (f ā coadj _) ā map h ā¼ (g ā coadj _) ā map i <<
                 āŖ assoc-l-ā āā¼ā assoc-l-ā ā«

    module _ {a : āØ š ā©} {b c : āØ š ā©} where
      module _ {f : a ā¶ āØ G ā© b} {g h : b ā¶ c} where
        destruct-precomp-free : (free f ā g ā¼ free f ā h) -> f ā map g ā¼ f ā map h
        destruct-precomp-free p = pā
          where
            pā = p
                 >> free f ā g ā¼ free f ā h <<

                 āŖ cong-ā¼ ā«

                 -- >> map (free f ā g) ā¼ map (free f ā h) <<

                 āŖ functoriality-ā āā¼ā functoriality-ā ā«

                 -- >> map (free f) ā map g ā¼ map (free f) ā map h <<

                 -- >> map (map f ā adj) ā map g ā¼ map (map f ā adj) ā map h <<

                 āŖ functoriality-ā ā refl āā¼ā
                   functoriality-ā ā refl ā«

                 -- >> map (map f) ā map adj ā map g ā¼ map (map f) ā map adj ā map h <<

                 āŖ refl ā_ ā«

                 -- >> coadj ā (map (map f) ā map adj ā map g) ā¼ coadj ā (map (map f) ā map adj ā map h) <<

                 āŖ assoc-[abcd]ā¼a[bcd]-ā ā»Ā¹ āā¼ā
                   assoc-[abcd]ā¼a[bcd]-ā ā»Ā¹ ā«

                 -- >> coadj ā map (map f) ā map adj ā map g ā¼ coadj ā map (map f) ā map adj ā map h <<

                 āŖ naturality f ā refl ā refl āā¼ā
                   naturality f ā refl ā refl ā«

                 -- >> f ā coadj ā map adj ā map g ā¼ f ā coadj ā map adj ā map h <<

                 āŖ assoc-[abcd]ā¼a[bc]d-ā āā¼ā
                   assoc-[abcd]ā¼a[bc]d-ā ā«

                 -- >> f ā (coadj ā map adj) ā map g ā¼ f ā (coadj ā map adj) ā map h <<

                 āŖ refl ā reduce-coadj ā refl āā¼ā
                   refl ā reduce-coadj ā refl ā«

                 -- >> f ā id ā map g ā¼ f ā id ā map h <<

                 āŖ unit-r-ā ā refl āā¼ā
                   unit-r-ā ā refl ā«

                 >> f ā map g ā¼ f ā map h <<
