
{-# OPTIONS --cubical --allow-unsolved-metas #-}

module Verification.Conventions.Meta.Structure where

open import Verification.Conventions.Prelude
open import Verification.Conventions.Meta.Term


open PrimitiveUniverseNotation



-- module _ (A : π° π) where
--   record IField : π° π where
--     field -_ : A -> A
--           _+_ : A -> A -> A
--           _*_ : A -> A -> A
--   open IField {{...}} public


private
  module TestStructure where
    record IRing {π : π} (A : π° π) : π° π where
      field -_ : A -> A
            _+_ : A -> A -> A
            _*_ : A -> A -> A
    open IRing {{...}} public





-------------------------
-- Teles

Full = (String Γ Arg (Type Γ Pattern))

FullTele = List ((String Γ Arg (Type Γ Pattern)))
Tele = List (String Γ Arg Type)


teleFromFullTele : FullTele -> Tele
teleFromFullTele = map-List (second (map-Arg fst))

matchesFromFullTele : FullTele -> List (Arg Pattern)
matchesFromFullTele = map-List (Ξ» (_ , a) -> map-Arg snd a)

makePiType : Tele -> Type -> Type
makePiType [] Ο = Ο
makePiType ((ar , a) β· tele) Ο = pi a (Abs.abs ar (makePiType tele Ο))

-------------------------
-- making implicit variables visible

intoVisible : β{A : π° π} -> Visibility -> Arg A -> Arg A
intoVisible v (arg (arg-info visible r) x) = arg (arg-info v r) x
intoVisible v (arg (arg-info hidden r) x) = arg (arg-info v r) x
intoVisible v (arg (arg-info instanceβ² r) x) = arg (arg-info instanceβ² r) x

makeVisible : Visibility -> β -> FullTele -> FullTele
makeVisible v i tele = rev (makeVisible' i (rev tele))
  where
    makeVisible' : β -> FullTele -> FullTele
    makeVisible' zero [] = []
    makeVisible' zero ((a , ar) β· xs) = (a , intoVisible v ar) β· xs
    makeVisible' (suc i) [] = []
    makeVisible' (suc i) (x β· xs) = x β· makeVisible' i xs

makeVisibleMany : Visibility -> List β -> FullTele -> FullTele
makeVisibleMany v [] tele = tele
makeVisibleMany v (n β· ns) tele = makeVisibleMany v ns (makeVisible v n tele)

makeVisibleAll : Visibility -> FullTele -> FullTele
makeVisibleAll v tele = map-List (second (intoVisible v)) tele

isUsedInOtherVisibles : β -> FullTele -> String -> Bool
isUsedInOtherVisibles i tele main = isUsedInOtherVisibles' i (rev tele) main
  where
    isUsedInOtherVisibles' : β -> FullTele -> String -> Bool
    isUsedInOtherVisibles' i [] main = false
    isUsedInOtherVisibles' (zero) _ _ = false -- ((a , ar) β· tele) main with a β main
    isUsedInOtherVisibles' (suc i) ((a , ar) β· tele) main with a β main
    ... | true = isUsedInOtherVisibles' i tele main
    ... | false with i β?-List (getVars visible (unArg ar .fst))
    ... | true = true
    ... | false = isUsedInOtherVisibles' i tele main

-------------------------
-- merge level variables

isDef : Term -> Name -> Bool
isDef (def f args) n = f β n
isDef x n = false

isDefInTele : (String Γ Arg (Type Γ Pattern)) -> Name -> Bool
isDefInTele ((_ , arg i (Ο , _))) n = isDef Ο n

isVisibleInTele : Full -> Bool
isVisibleInTele (_ , arg (arg-info visible r) _) = true
isVisibleInTele (_ , arg (arg-info hidden r) _) = false
isVisibleInTele (_ , arg (arg-info instanceβ² r) _) = false

prodInTele : Full -> Full -> Full
prodInTele (xs , arg i (xΟ , xpat)) (ys , arg j (yΟ , ypat)) = (xs <> "-" <> ys) , (arg i (def (quote _Γ_) (varg xΟ β· varg yΟ β· []) , ypat))

ΟβVar : β -> List (Arg Term) -> Term
ΟβVar i args = def (quote fst) (varg (var i []) β· args)

ΟβVar : β -> List (Arg Term) -> Term
ΟβVar i args = def (quote snd) (varg (var i []) β· args)

-- ΟβInTele : Full -> List (Arg Term) -> Term
-- ΟβInTele (_ , arg _ (t , _)) args = def (quote snd) args


-- substitution in tele

tesubstPattern : SSub -> Pattern -> Pattern
tesubstPattern (i , Ο) (con c ps) = absurd 0
tesubstPattern (i , Ο) (dot t) = absurd 0
tesubstPattern (i , Ο) (var x) = var (lowerAbove (suc i) x)
tesubstPattern (i , Ο) (lit l) = lit l
tesubstPattern (i , Ο) (proj f) = proj f
tesubstPattern (i , Ο) (absurd a) = absurd a

tesubstFull : SSub -> Full -> Full
tesubstFull Ο (s , arg info (a , b)) = (s , arg info (tesubst Ο a , tesubstPattern Ο b))

tesubstFullTele : SSub -> FullTele -> FullTele
tesubstFullTele Ο [] = []
tesubstFullTele Ο (x β· tele) = tesubstFull Ο x β· tesubstFullTele (jumpOverAbs Ο) tele

replaceFull : SSub -> Full -> Full
replaceFull Ο (s , arg info (a , b)) = (s , arg info (replace Ο a , b))

replaceFullTele : SSub -> FullTele -> FullTele
replaceFullTele Ο [] = []
replaceFullTele Ο (x β· tele) = replaceFull Ο x β· replaceFullTele (jumpOverAbs Ο) tele

{-# TERMINATING #-}
mergeLevelVars : (FullTele) -> ((β -> Type -> Type) Γ FullTele)
mergeLevelVars ([]) = β (Ξ» x -> x) , []
mergeLevelVars (x β· []) = β (Ξ» x -> x) , x β· []
mergeLevelVars (x β· y β· tele) with isDefInTele x (quote π) and isDefInTele y (quote Ξ£) and isVisibleInTele x and isVisibleInTele y
... | false =
  let (Ο , tele) = mergeLevelVars (y β· tele)
  in Ο , (x β· tele)
... | true  =
  let (dΟ , tele) = mergeLevelVars (tele)
      ntele = prodInTele x y β· tesubstFullTele (0 , ΟβVar 0) (replaceFullTele (1 , ΟβVar 1) tele)
      i0 = length-List tele
      ndΟ = Ξ» extra Ο -> let i = i0 +-β extra
                         in tesubst (i , ΟβVar i) (replace ((suc i) , ΟβVar (suc i)) (dΟ extra Ο))
  in ndΟ , ntele



getLevelN : β -> TC Term
getLevelN zero = quoteTC (ββ)
getLevelN (suc i) = do
  l <- (getLevelN i)
  val <- (unquoteTC l)
  quoteTC (val βΊ')

sortIntoLevelTerm : Sort -> TC Term
sortIntoLevelTerm unknown = return unknown
sortIntoLevelTerm (set t) = return t
sortIntoLevelTerm (lit n) = getLevelN n
sortIntoLevelTerm (prop t) = return t
sortIntoLevelTerm (propLit n) = getLevelN n
sortIntoLevelTerm (inf n) = return unknown -- TODO: What do we actually have to do here?


extractSort : Term -> Maybe Sort
extractSort (agda-sort s) = just s
extractSort t = nothing

getLevel : Term -> TC Term
getLevel (agda-sort s) = sortIntoLevelTerm s
getLevel r = printErr ("Expected to find a π°, but found: " <> show r)

getLevelOfType : Term -> TC Term
getLevelOfType t = inferType t >>= normalise >>= getLevel



-- Args:
-- (current debrujin level : β)
-- (main argument to abstract over name : String)
-- (type of IStructure definition : Type)
-- Returns:
-- ( : Type
-- ....
--  sort of the created type : Sort
-- )

-- liftBelowTele : β -> Tele -> Tele
-- liftBelowTele i = ?

readTele : Type -> β Γ FullTele Γ List (Arg β) Γ Type
readTele (pi a (Abs.abs ar b)) with readTele b
... | i , mtel , mte , mty = suc i
                       , (((ar , (map-Arg (\x -> (x , var i)) a))) β· mtel)
                       -- , (map-Arg (β (suc i)) a β· mte)
                       , (map-Arg (β (i)) a β· mte)
                       , mty
readTele a = 0 , [] , [] , a





buildStruct : String -> Type -> (β Γ FullTele Γ List (Arg β) Γ Maybe (β Γ Arg Type) Γ Maybe Sort)
buildStruct mainArg (pi a (Abs.abs ar b)) with (mainArg βS ar) | (buildStruct mainArg b)
... | false | i ,  mtel , mte , mainPos , s = (suc i)
                                              -- , (Ξ» Ο -> pi a (Abs.abs ar (mty Ο)))
                                              -- , (((ar , a) , (map-Arg (β (var (i))) a)) β· mtel)
                                              , (((ar , (map-Arg (\x -> (x , var i)) a))) β· mtel)
                                              , (map-Arg (β (suc i)) a β· mte)
                                              , map-Maybe (first suc) mainPos
                                              , s
... | true | i , mtel , mte , mainPos , s  = i
                                              -- , (Ξ» Ο -> mty Ο) -- mty (liftTill i Ο))
                                              , mtel
                                              , mte
                                              , (just (0 , (map-Arg (liftMany i) a)))
                                              , (map-Maybe (lowerAtSort i) s)
buildStruct mainArg x = 0 , [] , [] , nothing , (extractSort x)




_`β`_ : Term -> Term -> Term
_`β`_ `i` `j` =
  let f = quote _β_
  in (def f (varg `i` β· varg `j` β· []))

makeLam : FullTele -> Term -> Term
makeLam [] t = t
makeLam (((s , arg (arg-info v rβ) r)) β· tele) t = lam v (Abs.abs s (makeLam tele t))

extractPredicate : Type -> Maybe Type
extractPredicate t = {!!}

-- | Return the universe of the carrier set, as well as the predicate
match-StructureCall : Term -> TC (Term Γ Term Γ Term Γ Term)
match-StructureCall (def (quote Structure) ((arg _ qi) β· (arg _ qj) β· (arg _ qA) β· (arg _ qP) β· _)) = return (qi , qj , qA , qP)
  -- printErr ("Found the predicate: " <> show qP)
match-StructureCall s = printErr (show s <> "\nis not a structure on a predicate.")

-- macro
-- a  #openstruct-test : Name -> Term -> TC `π`
-- a  #openstruct-test name-Inst hole =
--     do
--       type-Inst <- getType name-Inst
--       type-Inst <- withReconstructed (return type-Inst)
--       type-Inst <- normalise type-Inst
--       pred-Term <- match-StructureCall type-Inst

--       `β` <- quoteTC β
--       unify hole `β`


macro
  #openstruct : Name -> Term -> TC π-π°
  #openstruct name-Inst hole =
    do
      type-Inst <- getType name-Inst
      type-Inst <- withReconstructed (return type-Inst)
      type-Inst <- normalise type-Inst
      let (i , mtel , mte , res-Type) = readTele type-Inst
      let mtel = makeVisibleAll (hidden) mtel
      let args = mte
      let args = map-List (map-Arg (Ξ» n -> var n [])) args

      -- | Full term for getting a "Structure P" value
      let structure-Term = (def name-Inst args)

      -- | Tele and variable matchlist for function definition
      let tele = teleFromFullTele mtel
      let varmatches = matchesFromFullTele mtel

      -- | Extracting the predicate from the structure call in the result type
      (carrier-level-Term , pred-level-Term , carrier-Type , pred-Term) <- match-StructureCall res-Type

      -- | In a context of all given variables, apply the predicate to the
      -- carrier set, given by β¨_β©
      Ξ1 <- getContext
      let Ξ2 = rev (tele)
      (res-Term , res-Type) <- inContext (Ξ1 <> Ξ2)
               do
                  carrier-level-Val <- unquoteTC carrier-level-Term
                  pred-level-Val <- unquoteTC pred-level-Term
                  carrier-Type-Val <- unquoteTC carrier-Type
                  pred-Term-Val <- unquoteTC pred-Term

                  structure-Val <- unquoteTC (structure-Term)

                  let Carrier = (β¨_β© {carrier-level-Val}
                                     {pred-level-Val}
                                     {carrier-Type-Val}
                                     {pred-Term-Val}
                                     structure-Val)

                  let pred-Type-Val = (carrier-Type-Val -> π°' pred-level-Val)
                  pred-Val <- assertType pred-Type-Val $ unquoteTC pred-Term

                  let istructure-Type-Val = pred-Val Carrier
                  istructure-Type <- quoteTC istructure-Type-Val >>= normalise

                  let istructure-Val = (of_ {carrier-level-Val}
                                        {pred-level-Val}
                                        {carrier-Type-Val}
                                        {pred-Term-Val}
                                        structure-Val)

                  istructure-Term <- quoteTC istructure-Val >>= normalise
                  return (istructure-Term , istructure-Type)

      let fullType = makePiType tele res-Type


      let fun = res-Term
      let StrFun = clause tele varmatches fun

      let term-Inst = pat-lam (StrFun β· []) []

      hole-Type <- inferType hole
      unify hole-Type fullType
      unify hole term-Inst
      return tt


      -- `β` <- quoteTC β
      -- unify hole `β`

      {-
      let fullType = makePiType tele resType


      let fun = (def name-Inst args)
      let StrFun = clause tele varmatches fun

      let term-Inst = pat-lam (StrFun β· []) []

      hole-Type <- inferType hole
      unify hole-Type fullType
      unify hole term-Inst
      return tt
      -}


module TestInstancing where
  private
    record MyRec (A : π°β) : π°β where
      field invert : A -> A

    open MyRec {{...}}
    getMyRec : (A : π°β) -> MyRec A
    MyRec.invert (getMyRec A) = \x -> x
    -- instance _ = Ξ» {A} -> getMyRec A
    -- instance _ = #openstruct getMyRec



#struct : String -> Name -> String -> Name -> Name -> TC π-π°
#struct _ name-IStructure mainArg name-Structure name-ctor =
  do
     ``π`` <- quoteTC π-π°
     `tt` <- quoteTC {A = π-π°} tt

     type-IStructure <- (getType name-IStructure)
     type-IStructure <- withReconstructed (return type-IStructure)
     type-IStructure <- normalise type-IStructure

     let (i , mtel , mte , mainPos , lastSort) = buildStruct mainArg type-IStructure
     mainPos <- liftTCMaybe mainPos ("Did not find argument with name " ++ mainArg)
     lastSort <- liftTCMaybe lastSort ("Could not extract level of structure target universe.")

     -- | type of main argument
     let type-mainArg = unArg (mainPos .snd)

     -- | Tele optimizations
     -- 1. make hidden, but not inferable variables visible
     let varsOfMain = getVars visible type-mainArg
     let varsToHide = filter (Ξ» i -> not (isUsedInOtherVisibles i mtel mainArg)) varsOfMain
     let mtel = makeVisibleMany visible varsToHide mtel
     -- 2. join Level variables which are near each other
     let dΟ-merge , mtel = mergeLevelVars mtel
     let type-mainArg = dΟ-merge 0 type-mainArg

     -- | The arguments to call the IStructure with
     let args = insertList (mainPos .fst) (map-Arg {A = Type} {B = β} (β zero) (mainPos .snd)) mte
     let args = map-List (map-Arg (Ξ» n -> var n [])) args
     let args = map-List (map-Arg (dΟ-merge 1)) args -- merge the πs

     -- | Tele and variable matchlist for function definition
     let tele = teleFromFullTele mtel
     let varmatches = matchesFromFullTele mtel


     -- printErr ("varsOfMain is: " <> show varsOfMain)
     -- printErr ("tele is: " <> show tele)
     -- printErr ("args is: " <> show args)
     -- printErr ("varmatches is: " <> show varmatches)
     -- printErr ("type-mainArg is: " <> show type-mainArg)

     -- | Skip the first args/tele/matches if we have them in our global tele
     Ξ1 <- getContext
     let args = skip-List (length-List Ξ1) args
     let tele = skip-List (length-List Ξ1) tele
     let varmatches = skip-List (length-List Ξ1) varmatches


     -- printErr ("type-mainArg is: " <> show type-mainArg <> "\n\n and checking in context:\n" <> show (Ξ1 <> Ξ2))
     -- | Computing the result type

     Ξ1 <- getContext
     let Ξ2 = rev (tele)
     `π` <- inContext (Ξ2 <> Ξ1)
                      do type-mainArg <- normalise type-mainArg
                         -- curΞ <- getContext
                         -- printErr ("we are in Ξ: " <> show curΞ)
                         getLevelOfType type-mainArg



     -- | Generate the return type
     `π` <- sortIntoLevelTerm lastSort
     let `π` = dΟ-merge 0 `π`
     let resType = (agda-sort (set (`π` `β` `π`)))
     let fullType = makePiType tele resType


     -- printErr ("varsOfMain is: " <> show varsOfMain)
     -- printErr ("tele is: " <> show tele)
     -- printErr ("args is: " <> show args)
     -- printErr ("varmatches is: " <> show varmatches)
     -- printErr ("fullType is: " <> show fullType)
     -- printErr ("resType is: " <> show resType)

     let funArgs = (harg (`π`) β· harg `π` β· harg (type-mainArg) β· varg (lam visible (Abs.abs "MyA" (def name-IStructure args))) β· [])
     let fun = (def (quote Structure) funArgs)
     let StrFun = clause tele varmatches fun

     declareDef (varg name-Structure) fullType
     defineFun name-Structure (StrFun β· [])

     --------------------------------------------------------------------
     -- | Generate the constructor

     let mtel = makeVisibleAll hidden mtel
     let tele = teleFromFullTele mtel
     let varmatches = matchesFromFullTele mtel

     -- | Skip the first args/tele/matches if we have them in our global tele
     Ξ1 <- getContext
     -- let args = skip-List (length-List Ξ1) args -- DONT NEED THIS. We did this already above.
     let tele = skip-List (length-List Ξ1) tele
     let varmatches = skip-List (length-List Ξ1) varmatches

     -- let tele2 = Ξ· ("A" , varg type-mainArg) <> Ξ· ("Impl" , varg (def name-IStructure args))
     let tele2 = Ξ· ("A" , varg type-mainArg) <> Ξ· ("Impl" , iarg (def name-IStructure args)) -- CORRECT LINE
     let tele-ctor = tele <> tele2
     let returnType-ctor = liftFrom 0 (liftFrom 0 fun)

     let type-ctor = makePiType tele-ctor returnType-ctor

     -- let varmatches2 = (varg (var 1) β· varg (var 0) β· [])
     let varmatches2 = (varg (var 1) β· iarg (var 0) β· []) -- THIS IS THE CORRECT LINE
     let varmatches-ctor = liftPats (liftPats varmatches) <> varmatches2

     -- let term-ctor = con (quote β²_β²) ((varg (var 1 []) β· varg (var 0 []) β· []))
     let term-ctor = con (quote β²_β²) ((varg (var 1 []) β· iarg (var 0 []) β· [])) -- CORRECT LINE
     let clause-ctor = clause tele-ctor varmatches-ctor term-ctor

     -- printErr ("varsOfMain is: " <> show varsOfMain)
     -- printErr ("varmatches is: " <> show varmatches)
     -- printErr ("tele is: " <> show tele)
     -- printErr ("tele-ctor is: " <> show tele-ctor)
     -- printErr ("term-ctor is: " <> show term-ctor)
     -- printErr ("type-ctor is: " <> show type-ctor)
     -- printErr ("varmatches-ctor is: " <> show varmatches-ctor)


     declareDef (varg name-ctor) type-ctor
     defineFun name-ctor (clause-ctor β· [])

     -- declareDef (varg name-ctor) (``π``)
     -- defineFun name-ctor (clause [] [] (`tt`) β· [])

     return tt




-- open import Verification.Conventions.Category.Base

private
  record IFunctor (X : π° π) (Y : π° π) (F : X -> Y) : π° (π ο½€ π) where
  module _ (A : π° π) (B : π° π) (C : π° π) where
    -- record IMap (f : A -> B) : π°β where
    -- unquoteDecl Map map = #struct "?" (quote IMap) "f" Map map

    record IMapi (f : A -> B) (g : A -> B) (p : f β‘ g) : π°β where
    unquoteDecl Mapi mapi = #struct "?" (quote IMapi) "p" Mapi mapi

-- Good tests:
  unquoteDecl Functor functor = #struct "?" (quote IFunctor) "F" Functor functor
  unquoteDecl Ring ring = #struct "?" (quote TestStructure.IRing) "A" Ring ring
unquoteDecl MFun mfun = #struct "?" (quote IFunctor) "F" MFun mfun


-- instance
--   Structure:Impl : β{A : π° π} {P : A -> π° π} -> β{x : Ring π} -> TestStructure.IRing β¨ x β©
--   Structure:Impl = {!!}



  -- -- unquoteDecl MCat mcat = #struct (quote ICategory) "X" MCat mcat

-- unquoteDecl MNat mnat = #struct (quote ITransformation) "Ξ±" MNat mnat



-- unquoteDecl Field makeField = #struct (quote IField) "A" Field makeField


-- test123 : (X Y : MCat (ββ , ββ , ββ ,-)) -> (a b c : β¨ X β©) -> (f : Hom a b) -> (g : Hom b c) -> Hom a c
-- test123 X Y a b c f g = f β g


open TestStructure
test : (R : Ring π) -> β¨ R β© -> β¨ R β©
test R a = a + a

{-
#struct2 : Name -> String -> Name -> Name -> TC π-π°
#struct2 nameI mainArg a b =
  do
     ``π`` <- quoteTC π-π°
     `tt` <- quoteTC tt

     defT <- (getType nameI)
     defT2 <- withReconstructed (return defT)

     -- printErr (show defT2)

     -- res <- withNormalisation true do
     --    -- defI <- withReconstructed (getDefinition nameI)
     --    return tt

     declareDef (varg a) (``π``)
     defineFun a (clause [] [] (`tt`) β· [])

     declareDef (varg b) (``π``)
     defineFun b (clause [] [] (`tt`) β· [])

     return tt
-}

    -- dothis : β -> β
    -- dothis n = invert n



-- test : ring β‘ tt
-- test = refl



-- Ring : β(π : π) -> π° (π βΊ)
-- Ring π = Structure (IRing {π})

-- ring : β{A : π° β}



-- sum3 : {A : Ring π} -> (a : β¨ A β©) -> β¨ A β©
-- sum3 a = (a + a) + a


-- record IStructure {A : π° π} (P : A -> π° π) (Q : π° π) : π° (π β π β π) where
--   field _β : (a : A) -> {{p : P a}} -> Q
--   infixr 200 _β
-- open IStructure {{...}} public



-- xx2 = quoteTC ()




-- MyStruct-def : TC Definition
-- MyStruct-def =
--   do n <- freshName "MyStruct"
--      a1n <- freshName "arg1"
--      let a1 = arg (arg-info visible relevant) a1n
--      let myrec = record-type n (a1 β· [])
--      return myrec

-- abc = quoteTC `π`





-- makeMyStruct : (st-name : Name) -> TC `π`
-- makeMyStruct st-name = do
--   defineFun (varg )


-- unquoteDecl x = makeMyStruct x



