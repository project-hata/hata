
module Hata.Reflection.Definition where

open import Verification.Conventions
open import Verification.Conventions.Meta.Term
open import Hata.Builtin
open import Hata.Program.HataCmd.HataSystemInterface
open import Hata.Program.HataCmd.Edittime
open import Hata.Program.HataCmd.Common
open import Hata.Extern.Haskell.Generate

-- reflection targets
open import Hata.Reflection.Signature.Record
open import Hata.Reflection.Signature.Datatype

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

---------------------------------------------------------------------
-- reflection

data ReflectedObject : 𝒰₀ where
  ReflectedDatatype : DatatypeFOSignature -> ReflectedObject
  ReflectedRecord : RecordFOSignature -> ReflectedObject

module _ where
  private
    reflect : Name -> Definition -> TC ReflectedObject
    reflect n d@(data-type pars cs) = do
      Σ <- reflectIntoDatatypeSignature n d
      return (ReflectedDatatype Σ)
    reflect n d@(record-type c fs) = do
      Σ <- reflectIntoRecordSignature n d
      return (ReflectedRecord Σ)
    -- reflect n (data-cons d) = {!!}
    -- reflect n axiom = {!!}
    -- reflect n prim-fun = {!!}
    reflect n x = throwError ("The definition of " <> show n <> " cannot be reflected.")

  macro
    #reflect : Name -> Term -> TC 𝟙-𝒰
    #reflect object-name hole = do
      object-def <- getDefinition object-name
      object-reflected <- reflect object-name object-def
      object-reflected-quoted <- quoteTC object-reflected
      unify hole object-reflected-quoted

------------------------------------------
-- misc

open import Hata.Abstract.Path.Definition renaming (Abs to AAbs)

sln-root : TC ((AAbs , Dir)-Path)
sln-root = return (:: / "hello")

macro
  # : ∀{A : 𝒰 𝑖} -> TC A -> Term -> TC 𝟙-𝒰
  # f hole = do
    res <- f
    res-quoted <- quoteTC res
    unify hole res-quoted

------------------------------------------
-- projects

TypeMap : 𝒰₁
TypeMap = List (𝒰₀ ×-𝒰 𝒰₀ ×-𝒰 Text)

record isProjectType (A : 𝒰₀) : 𝒰₁ where
  field
    SingleFile : 𝒰₀
    IdentMapping : TypeMap -> 𝒰₀
    generateProjectFile : (TM : TypeMap) -> SingleFile -> (AAbs , Mod)-Path -> (Text ×-𝒰 IdentMapping TM)
    projectFilePath : A -> (AAbs , Mod)-Path -> (AAbs , File)-Path

open isProjectType public

generateFile : (TM : TypeMap) -> {A : 𝒰₀} {{AP : isProjectType A}} -> (a : A) -> SingleFile AP -> (AAbs , Mod)-Path -> TC (IdentMapping AP TM)
generateFile TM {{AP}} a file path = do
  let txt , map = generateProjectFile AP TM file path
  let path-file = projectFilePath AP a path
  --- write to file
  return map

---------------------------------------------------------------------
-- Next steps:
--
-- [[For a reflected HIO execution system]]
--
-- A) HIO 1
-- 0. abstract existing reflection generation code over different things to be reflected
-- 0.5. add arg to control where the result is generated
-- 0.7. for haskell bindings we also have to say where the agda code has to be generated
--      that is for Hs->Ag it has to be in the same file in a marked block
-- 1. generate haskell files for data type signatures
-- 2. generate agda haskell bindings for data type signatures
-- 3. ACTUALLY, generate bindings for HIO data type
-- 4. use ad-hoc binding for HIO -> TCMEXEC execution
--
-- B) HIO 2: Now implementation of IO binding for HIO tasks
-- 5. allow for reflection of postulate functions
-- 6. generate Hs->Ag bindings for these functions
-- 7. ACTUALLY, generate binding for HIO evaluation
-- 8. NOTE: this is special generation of templates; for the function needs to be
--    implemented in haskell. Think about how this can be done in a user friendly way.
--
-- C) Commands to HataDaemon
-- 9. OPTIONAL Generate JSON printing of reflected datatype / record in TC
-- 10. Generate rust code for records / datatypes (with json parsing)
-- 11. Implement code to execute these (translated) `DaemonCommand`s
-- 12. Call these DaemonCommands from AgdaCmd with haskells json generation
--
-- D) Better HataDaemon UI
-- 13. Add multiple message/log-views for different hata interaction states
--
-- E) Syntax generation
-- 14. Given a reflected datatype, generate a rust treesitter project that parses it
-- 15. Somehow describe how we can connect this project to other things.
--      - Different connection possibilities: via cmd, via direct library binding
--
-- F) Library integration
-- 16. Define external C libraries. Allow them to be binded into Hata, or into
--     other binding targets.
--
--
-- ---------------------------------------------------------------------
-- Pattern:
-- - All interfaces between languages are written in Agda, and the actual
--   language files are generated. Other things may be required to be implemented
--   in the given language.
-- - For external projects that use hata, the usage-pattern can be the following:
--   in the .metabuild-root (or rather .hata-root) it is defined where the agda files
--   are that describe the interfaces between the languages. Or rather, that describe
--   how the different languages fit together to make up a project.
--   This is used by the metabuilder to create a "building plan".
-- - Every "Hata Project" has an "Agda core", which allows for interactivity with
--   the differenct language components of the project.
-- - This means that the file should rather be called "cubelang.hataprj"
--    - In this file it is described where the (agda-)project definitions are
--    - All these definitions are the primary watch targets for metabuilder
-- - There is a way to run agda code from haskell. By generating a temporary file
--   that contains EXECTCM code that typechecks the given file and then sends
--   the result back via HataCmd.
-- - This way, external projects can built.
--


