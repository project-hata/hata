
module Impure.Reflection.Definition where

open import Verification.Conventions
open import Verification.Conventions.Meta.Term
open import Impure.Builtin
open import Impure.Program.HataCmd.HataSystemInterface
open import Impure.Program.HataCmd.Edittime
open import Impure.Program.HataCmd.Common
open import Impure.Extern.Haskell.Generate

-- reflection targets
open import Impure.Reflection.Signature.Record
open import Impure.Reflection.Signature.Datatype

sequence : ∀{A : 𝒰 𝑖} -> List (TC A) -> TC (List A)
sequence [] = return []
sequence (x ∷ xs) = do
  x' <- x
  xs' <- sequence xs
  return (x' ∷ xs')

dropLast : ∀{A : 𝒰 𝑖} -> List A -> List A
dropLast [] = []
dropLast (x ∷ []) = []
dropLast (x ∷ y ∷ xs) = x ∷ dropLast (y ∷ xs)

mapM : ∀{A : 𝒰 𝑖} {B : 𝒰 𝑗} -> (A -> TC B) -> List A -> TC (List B)
mapM f xs = sequence (map-List f xs)

private
  throwError : ∀{a : 𝒰 𝑖} -> Text -> TC a
  throwError str = typeError (strErr str ∷ [])

  unAbs : ∀{a : 𝒰 𝑖} -> Abs a -> a
  unAbs (Abs.abs s x) = x

  expectArr : Type -> TC (Type ×-𝒰 Type)
  expectArr (pi a b) = return (unArg a , unAbs b)
  expectArr x = throwError ("expected an arrow type, but got: " <> show x)

  expectMultiArr : Type -> TC (List Type)
  expectMultiArr (pi a (Abs.abs s x)) = do
    xs <- expectMultiArr x
    return $ unArg a ∷ xs
  expectMultiArr _ = return []

  showType : Type -> TC Text
  showType (def f args) = call-hsi-getNameFromFQ f
  showType ty = throwError ("unsupported " <> show ty)


  ---------------------------------------------------------------------
  -- records
  reflectRecordField : Name -> TC (Text ×-𝒰 Text)
  reflectRecordField n = do
    n' <- call-hsi-getNameFromFQ n
    (_ , ty) <- getType n >>= expectArr
    ty' <- showType ty
    return (n' , ty')

  reflectIntoRecordSignature : Name -> Definition -> TC RecordFOSignature
  reflectIntoRecordSignature n (record-type c fs) = do
    sort' <- call-hsi-getNameFromFQ n
    modulePath' <- call-hsi-getModuleFromFQ n
    fields' <- mapM reflectRecordField (map-List unArg fs)
    return $ record
      { sort = sort'
      ; fields = fields'
      ; modulePath = modulePath'
      }
  reflectIntoRecordSignature _ _ = typeError (strErr "Expected a record definition." ∷ [])


  ---------------------------------------------------------------------
  -- data types
  reflectDatatypeCtor : Name -> TC (Text ×-𝒰 List Text)
  reflectDatatypeCtor n = do
    n' <- call-hsi-getNameFromFQ n
    arrtys <- getType n >>= expectMultiArr
    let arrargs = dropLast arrtys
    tys <- mapM showType arrargs
    return (n' , tys)

  reflectIntoDatatypeSignature : Name -> Definition -> TC DatatypeFOSignature
  reflectIntoDatatypeSignature n (data-type pars cs) = do
    sort' <- call-hsi-getNameFromFQ n
    modulePath' <- call-hsi-getModuleFromFQ n
    ctors' <- mapM reflectDatatypeCtor cs
    return $ record
      { sort = sort'
      ; modulePath = modulePath'
      ; ctors = ctors'
      }
  reflectIntoDatatypeSignature _ _ = typeError (strErr "Expected a datatype definition." ∷ [])



notice =
  "\n\
  \---------------------------------------------------------------\n\
  \---------- v v v v     AUTO GENERATED        v v v v ----------\n\
  \---------------------------------------------------------------\n"
notice2 =
  "--  -----------------\n\
  \--  |\n\
  \--  | GENERATED CODE for haskell bindings is here.\n\
  \--  v\n\
  \--------------------------------------------------\n"

macro
  #generate-haskell : Name -> Term → TC 𝟙-𝒰
  #generate-haskell object-name s = do
    object-def <- getDefinition object-name
    Σ <- reflectIntoRecordSignature object-name object-def

    let file = generateRecordFile Σ
    let bindings = generateHaskellBindings Σ
    call-ET-writeGeneratedHaskellFile ("HataGeneratedModules.Types." <> modulePath Σ) file
    call-ET-updateAgdaDatatypeSourceFile (modulePath Σ) ("_ = #generate-haskell") (notice2 <> bindings)

    unify s (lit (string ""))




