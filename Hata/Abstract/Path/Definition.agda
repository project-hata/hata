
module Hata.Abstract.Path.Definition where

open import Hata.Conventions

data RootType : 𝒰₀ where
  Rel Abs : RootType

data FSLeaf : 𝒰₀ where
  Dir File : FSLeaf
  HsProj : FSLeaf

data ModLeaf : 𝒰₀ where
  Mod : ModLeaf

record isLeafType (N : 𝒰₀) : 𝒰₁ where
  field _-Name : N -> 𝒰₀
  field defaultNode : N
  field _switchTo_ : N -> N -> 𝒰₀

open isLeafType {{...}} public

data FileName : 𝒰₀ where
  _∶_ : Text -> Text -> FileName

data HsProjName : 𝒰₀ where
  hsproj : Text -> HsProjName

infix 70 _∶_

FSName : FSLeaf -> 𝒰₀
FSName Dir = Text
FSName File = FileName
FSName HsProj = HsProjName

ModName : ModLeaf -> 𝒰₀
ModName Mod = Text

data switchToFS : FSLeaf -> FSLeaf -> 𝒰₀ where
  instance dirToDir : switchToFS Dir Dir
  instance dirToFile : switchToFS Dir File
  instance dirToHsProj : switchToFS Dir HsProj
  -- instance dirToMod : switchToFS Dir Mod
  -- instance fileToMod : switchToFS File Mod
  -- instance modToMod : switchToFS Mod Mod

data switchToMod : ModLeaf -> ModLeaf -> 𝒰₀ where
  instance modToMod : switchToMod Mod Mod

instance
  isLeafType:LeafType : isLeafType FSLeaf
  isLeafType:LeafType = record
    { _-Name = FSName
    ; defaultNode = Dir
    ; _switchTo_ = switchToFS
    }

instance
  isLeafType:ModType : isLeafType ModLeaf
  isLeafType:ModType = record
    { _-Name = ModName
    ; defaultNode = Mod
    ; _switchTo_ = switchToMod
    }


-- data _-Name : FSLeaf -> 𝒰₀ where

module _ {R N : 𝒰₀} {{_ : isLeafType N}} where
  -- infix 50  _∶/
  infixl 30  _/_
  data _-Path : (R × N) -> 𝒰₀ where
    :: : {r : R} -> (r , defaultNode)-Path
    -- relpath:_ : (Rel , Dir)-Path
    -- abspath:_ : (Abs , Dir)-Path
    _/_ : ∀{p x y} -> (p , x)-Path -> (y)-Name -> {{_ : x switchTo y}} -> (p , y)-Path


concat : ∀{x : FSLeaf} -> (Abs , Dir)-Path -> (Rel , x)-Path -> (Abs , x)-Path
concat root :: = root
concat root (next / x) = concat root next / x

toFilePath : ∀{x : FSLeaf} -> (Abs , x)-Path -> Text
toFilePath :: = ""
toFilePath {Dir} (p / next) = toFilePath p <> "/" <> next
toFilePath {File} (p / x ∶ ty) = toFilePath p <> "/" <> x <> "." <> ty
toFilePath {HsProj} (p / hsproj next) = toFilePath p <> "/" <> next


mypath : (Rel , File)-Path
mypath = :: / "bla" / "hello" ∶ "png"


