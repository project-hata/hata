
module Verification.Impure.Abstract.Path.Definition where

open import Verification.Impure.SpecialConventions

data RootType : 𝒰₀ where
  Rel Abs : RootType

data LeafType : 𝒰₀ where
  Dir File : LeafType
  Mod : LeafType

record isLeafType (N : 𝒰₀) : 𝒰₁ where
  field _-Name : N -> 𝒰₀
  field defaultNode : N
  field _switchTo_ : N -> N -> 𝒰₀

open isLeafType {{...}} public

data FileName : 𝒰₀ where
  _∶_ : Text -> Text -> FileName

infix 70 _∶_

FSName : LeafType -> 𝒰₀
FSName Dir = Text
FSName File = FileName
FSName Mod = Text

data switchToFS : LeafType -> LeafType -> 𝒰₀ where
  instance dirToDir : switchToFS Dir Dir
  instance dirToFile : switchToFS Dir File
  -- instance dirToMod : switchToFS Dir Mod
  -- instance fileToMod : switchToFS File Mod
  -- instance modToMod : switchToFS Mod Mod

instance
  isLeafType:LeafType : isLeafType LeafType
  isLeafType:LeafType = record
    { _-Name = FSName
    ; defaultNode = Dir
    ; _switchTo_ = switchToFS
    }


-- data _-Name : LeafType -> 𝒰₀ where

module _ {R N : 𝒰₀} {{_ : isLeafType N}} where
  -- infix 50  _∶/
  infixl 30  _/_
  data _-Path : (R × N) -> 𝒰₀ where
    :: : {r : R} -> (r , defaultNode)-Path
    -- relpath:_ : (Rel , Dir)-Path
    -- abspath:_ : (Abs , Dir)-Path
    _/_ : ∀{p x y} -> (p , x)-Path -> (y)-Name -> {{_ : x switchTo y}} -> (p , y)-Path




mypath : (Rel , File)-Path
mypath = :: / "bla" / "hello" ∶ "png"


