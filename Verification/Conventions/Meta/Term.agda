

module Verification.Conventions.Meta.Term where

open import Verification.Conventions.Prelude hiding (π ; π ; π ; π)
open import Agda.Builtin.Reflection public
open import Agda.Builtin.Char

open PrimitiveUniverseNotation

{-# TERMINATING #-}
cmpTerm : Term -> Term -> Bool

instance
  IBootEq:Term : IBootEq Term
  IBootEq._β_ IBootEq:Term = cmpTerm

instance
  IBootEq:Name : IBootEq Name
  IBootEq._β_ IBootEq:Name = primQNameEquality

  IBootEq:Meta : IBootEq Meta
  IBootEq._β_ IBootEq:Meta = primMetaEquality

instance
  IBootEq:Visibility : IBootEq Visibility
  IBootEq._β_ IBootEq:Visibility = _βV_
    where
      _βV_ : Visibility -> Visibility -> Bool
      visible βV visible = true
      hidden βV hidden = true
      instanceβ² βV instanceβ² = true
      _ βV _ = false


instance
  IBootEq:Relevance : IBootEq Relevance
  (IBootEq:Relevance IBootEq.β relevant) relevant = true
  (IBootEq:Relevance IBootEq.β relevant) irrelevant = false
  (IBootEq:Relevance IBootEq.β irrelevant) relevant = false
  (IBootEq:Relevance IBootEq.β irrelevant) irrelevant = true

  IBootEq:Quantity : IBootEq Quantity
  IBootEq._β_ IBootEq:Quantity quantity-0 quantity-0 = true
  IBootEq._β_ IBootEq:Quantity quantity-0 quantity-Ο = false
  IBootEq._β_ IBootEq:Quantity quantity-Ο quantity-0 = false
  IBootEq._β_ IBootEq:Quantity quantity-Ο quantity-Ο = true


  IBootEq:Modality : IBootEq Modality
  IBootEq._β_ IBootEq:Modality (modality r1 q1) (modality r2 q2) = (r1 β r2) and (q1 β q2)


instance
  IBootEq:ArgInfo : IBootEq ArgInfo
  (IBootEq:ArgInfo IBootEq.β arg-info v r) (arg-info w s) = (v β w) and (r β s)

  IBootEq:Arg : β{A : π° π} -> {{_ : IBootEq A}} -> IBootEq (Arg A)
  (IBootEq:Arg IBootEq.β arg i x) (arg j y) = (i β j) and (x β y)

  IBootEq:Abs : β{A : π° π} -> {{_ : IBootEq A}} -> IBootEq (Abs A)
  (IBootEq:Abs IBootEq.β Abs.abs s x) (Abs.abs t y) = x β y -- WARNING! We do ignore the strings here, because they should not be relevant

  IBootEq:Literal : IBootEq Literal
  (IBootEq:Literal IBootEq.β nat n) (nat m) = n β m
  (IBootEq:Literal IBootEq.β word64 n) (word64 m) = n β m
  (IBootEq:Literal IBootEq.β float x) (float y) = x β y
  (IBootEq:Literal IBootEq.β char c) (char d) = c β d
  (IBootEq:Literal IBootEq.β string s) (string t) = s β t
  (IBootEq:Literal IBootEq.β name x) (name y) = x β y
  (IBootEq:Literal IBootEq.β meta x) (meta y) = x β y
  (IBootEq:Literal IBootEq.β _) (_) = false


  IBootEq:Pattern : IBootEq Pattern
  (IBootEq:Pattern IBootEq.β con c ps) (con d ps2) = (c β d) and (ps β ps2)
  (IBootEq:Pattern IBootEq.β dot t) (dot s) = t β s
  (IBootEq:Pattern IBootEq.β var x) (var y) = x β y
  (IBootEq:Pattern IBootEq.β lit l) (lit m) = l β m
  (IBootEq:Pattern IBootEq.β proj f) (proj g) = f β g
  (IBootEq:Pattern IBootEq.β absurd x) (absurd y) = true -- WARNING! We ignore the x : β argument here, though I do not know what it means. (But it seems irrelevant)
  (IBootEq:Pattern IBootEq.β _) (_) = false

  IBootEq:Clause : IBootEq Clause
  (IBootEq:Clause IBootEq.β clause tel ps t) (clause tel2 ps2 t2) = (map-List snd tel β map-List snd tel2) and (ps β ps2) and (t β t2)
  (IBootEq:Clause IBootEq.β absurd-clause tel ps) (absurd-clause tel2 ps2) = (map-List snd tel β map-List snd tel2) and (ps β ps2)
  (IBootEq:Clause IBootEq.β _) (_) = false

  IBootEq:Sort : IBootEq Sort
  (IBootEq:Sort IBootEq.β set s) (set t) = s β t
  (IBootEq:Sort IBootEq.β lit n) (lit m) = n β m
  (IBootEq:Sort IBootEq.β unknown) unknown = true
  (IBootEq:Sort IBootEq.β _) _ = false




cmpTerm (var x args) (var y args2) = (x β y) and (args β args2)
cmpTerm (con c args) (con d args2) = (c β d) and (args β args2)
cmpTerm (def f args) (def g args2) = (f β g) and (args β args2)
cmpTerm (lam v t) (lam w s) = (v β w) and (t β s)
cmpTerm (pat-lam cs args) (pat-lam ds args2) = (cs β ds) and (args β args2)
cmpTerm (pi a b) (pi a2 b2) = (a β a2) and (b β b2)
cmpTerm (agda-sort s) (agda-sort t) = s β t
cmpTerm (lit l) (lit m) = l β m
cmpTerm (meta x y) (meta x2 y2) = (x β x2) and (y β y2)
cmpTerm unknown unknown = true
cmpTerm _ _ = false


assertType : β(a : π°' π) -> TC a -> TC a
assertType _ x = x



showImplicit = false

wrapVis : Visibility -> String -> String
wrapVis visible s = "(" <> s <> ")"
wrapVis hidden s with showImplicit
... | true = "{" <> s <> "}"
... | false = ""
wrapVis instanceβ² s = "{{" <> s <> "}}"

wrapRel : Relevance -> String -> String
wrapRel relevant s = s
wrapRel irrelevant s = "." <> s

wrapMod : Modality -> String -> String
wrapMod m s = s
-- wrapMod relevant s = s
-- wrapMod irrelevant s = "." <> s

wrapInfo : ArgInfo -> String -> String
wrapInfo (arg-info v r) s = wrapVis v (wrapMod r s)


instance
  IShow:Arg : β{A : π° π} -> {{_ : IShow A}} -> IShow (Arg A)
  IShow.show IShow:Arg (arg i x) = wrapInfo i (show x)

unArg : β{A : π° π} -> Arg A -> A
unArg (arg _ a) = a

findMainName : List Char -> List Char -> List Char
findMainName cur [] = cur
findMainName cur ('.' β· s) = findMainName [] s
findMainName cur (x β· s) = findMainName (cur <> (x β· [])) s

instance
  IShow:Name : IShow Name
  IShow.show IShow:Name s = primStringFromList (findMainName [] (primStringToList (primShowQName s)))

instance
  IShow:Meta : IShow Meta
  IShow.show IShow:Meta s = "meta" <> primShowMeta s

showListSpace : β{A : π° π} {{_ : IShow A}} -> List A -> String
showListSpace (xs) with show xs
... | "" = ""
... | t = " " <> t


instance
  {-# TERMINATING #-}
  IShow:Term : IShow Term

  IShow:Sort : IShow Sort
  IShow.show IShow:Sort (set t) = "π° (" <> show t <> ")"
  IShow.show IShow:Sort (lit n) = "π° " <> show n
  IShow.show IShow:Sort unknown = "?"
  IShow.show IShow:Sort (prop t) = "prop"
  IShow.show IShow:Sort (propLit n) = "propLit"
  IShow.show IShow:Sort (inf n) = "inf"

  IShow.show IShow:Term (var x args) = "(var " <> show x <> ")" <> showListSpace args
  IShow.show IShow:Term (con c args) = "ctor:" <> show c <> showListSpace args
  IShow.show IShow:Term (def f args) = show f <> showListSpace args
  IShow.show IShow:Term (lam v (Abs.abs s x)) = "(Ξ» " <> wrapVis v s <> " -> " <> show x <> ")"
  IShow.show IShow:Term (pat-lam cs args) = "<<pat>>"
  IShow.show IShow:Term (pi a (Abs.abs s x)) = "(Ξ  (" <> s <> " : " <> show a <> ") -> " <> show x <> ")"
  IShow.show IShow:Term (agda-sort s) = show s
  IShow.show IShow:Term (lit l) = "<<literal>>"
  IShow.show IShow:Term (meta x args) = show x <> showListSpace args
  IShow.show IShow:Term unknown = "?"

  IShow:Pattern : IShow Pattern
  IShow.show IShow:Pattern (con c ps) = "<<constr pattern>>"
  IShow.show IShow:Pattern (dot t) = "." <> show t
  IShow.show IShow:Pattern (var x) = "(var" <> show x <> ")"
  IShow.show IShow:Pattern (lit l) = "<<literal pattern>>"
  IShow.show IShow:Pattern (proj f) = "<< proj pattern >>"
  IShow.show IShow:Pattern (absurd _) = "()"

_βS_ = primStringEquality

_++_ = primStringAppend

infixl 40 _>>=_
_>>=_ = bindTC
return = returnTC
_>>_ : β{A B : π° π} -> (TC A) -> TC B -> TC B
_>>_ a b = a >>= \_ -> b

-- pattern varg x = arg (arg-info visible relevant) x
-- pattern harg x = arg (arg-info hidden  relevant) x
-- pattern iarg x = arg (arg-info instanceβ²    relevant) x

pattern varg x = arg (arg-info visible (modality relevant quantity-Ο)) x
pattern harg x = arg (arg-info hidden  (modality relevant quantity-Ο)) x
pattern iarg x = arg (arg-info instanceβ²    (modality relevant quantity-Ο)) x

printErr : β{A : π° π} -> String -> TC A
printErr s = typeError (strErr s β· [])

printType : β{A : π° π} -> Type -> TC A
printType Ο = typeError (termErr Ο β· [])

open TypeNotation public



-- Maybe : π° π -> π° π
-- Maybe A = β€ +-π° A

-- pattern just x = right x
-- pattern nothing = left tt

map-Arg : β{A B : π° π} -> (A -> B) -> Arg A -> Arg B
map-Arg f (arg i x) = arg i (f x)


-- map-Maybe : β{A B : π° π} -> (A -> B) -> Maybe A -> Maybe B
-- map-Maybe f (left x) = left x
-- map-Maybe f (right x) = right (f x)

map-Abs : β{A B : π° π} -> (A -> B) -> Abs A -> Abs B
map-Abs f (Abs.abs s x) = Abs.abs s (f x)

liftArgs : List (Arg β) -> List (Arg β)
liftArgs = map-List (map-Arg suc)

_β€?_ : β -> β -> Bool
zero β€? j = true
suc i β€? zero = false
suc i β€? suc j = i β€? j

-- === Lowering

lowerAbove : β -> β -> β
lowerAbove i j with i β€? j
... | false = j
lowerAbove i zero | true = zero
lowerAbove i (suc j) | true = j

lowerAt : β -> Type -> Type

{-# TERMINATING #-}
lowerAtVar : β -> β Γ List (Arg Term) -> β Γ List (Arg Term)
lowerAtVar i (j , ts) = lowerAbove i j , map-List (map-Arg (lowerAt i)) ts

lowerAtSort : β -> Sort -> Sort
lowerAtSort i (set t) = set (lowerAt i t)
lowerAtSort i (lit n) = lit n
lowerAtSort i unknown = unknown
lowerAtSort i (prop t) = prop (lowerAt i t)
lowerAtSort i (propLit n) = propLit n
lowerAtSort i (inf n) = inf n

lowerAt i (var x args) = let (x , args) = lowerAtVar i (x , args) in var x args
lowerAt i (con c args) = con c (map-List (map-Arg (lowerAt i)) args)
lowerAt i (def f args) = def f (map-List (map-Arg (lowerAt i)) args)
lowerAt i (lam v t) = lam v (map-Abs (lowerAt (suc i)) t)
lowerAt i (pat-lam cs args) = unknown
lowerAt i (pi a b) = pi (map-Arg (lowerAt i) a) (map-Abs (lowerAt (suc i)) b)
lowerAt i (agda-sort s) = agda-sort (lowerAtSort i s)
lowerAt i (lit l) = lit l
lowerAt i (meta x y) = unknown
lowerAt i unknown = unknown

-- === Lifting

liftBelow : β -> β -> β
liftBelow i j with suc j β€? i
... | false = j
... | true = suc j

liftFromTill : β -> β -> Type -> Type

{-# TERMINATING #-}
liftFromTillVar : β -> β -> β Γ List (Arg Term) -> β Γ List (Arg Term)
liftFromTillVar k i (j , ts) = liftBelow i j , map-List (map-Arg (liftFromTill k i)) ts

liftFromTillSort : β -> β -> Sort -> Sort
liftFromTillSort k i (set t) = set (liftFromTill k i t)
liftFromTillSort k i (lit n) = lit n
liftFromTillSort k i unknown = unknown
liftFromTillSort k i (prop t) = prop (liftFromTill k i t)
liftFromTillSort k i (propLit n) = propLit n
liftFromTillSort k i (inf n) = inf n

liftFromTill k i (var x args) = let (x , args) = liftFromTillVar k i (x , args) in var x args
liftFromTill k i (con c args) = con c (map-List (map-Arg (liftFromTill k i)) args)
liftFromTill k i (def f args) = def f (map-List (map-Arg (liftFromTill k i)) args)
liftFromTill k i (lam v t) = lam v (map-Abs (liftFromTill (suc k) i) t)
liftFromTill k i (pat-lam cs args) = unknown
liftFromTill k i (pi a b) = pi (map-Arg (liftFromTill k i) a) (map-Abs (liftFromTill (suc k) i) b)
liftFromTill k i (agda-sort s) = agda-sort (liftFromTillSort k i s)
liftFromTill k i (lit l) = lit l
liftFromTill k i (meta x y) = unknown
liftFromTill k i unknown = unknown

liftTill : β -> Type -> Type
liftTill = liftFromTill 0

liftTillSort : β -> Sort -> Sort
liftTillSort = liftFromTillSort 0

-- == Lifting from a value

liftAbove : β -> β -> β
liftAbove i j with i β€? j
... | false = j
... | true = suc j

liftFrom : β -> Type -> Type

{-# TERMINATING #-}
liftFromVar : β -> β Γ List (Arg Term) -> β Γ List (Arg Term)
liftFromVar i (j , ts) = liftAbove i j , map-List (map-Arg (liftFrom i)) ts

liftFromSort : β -> Sort -> Sort
liftFromSort i (set t) = set (liftFrom i t)
liftFromSort i (lit n) = lit n
liftFromSort i unknown = unknown
liftFromSort i (prop t) = prop (liftFrom i t)
liftFromSort i (propLit n) = propLit n
liftFromSort i (inf n) = inf n

liftFrom i (var x args) = let (x , args) = liftFromVar i (x , args) in var x args
liftFrom i (con c args) = con c (map-List (map-Arg (liftFrom i)) args)
liftFrom i (def f args) = def f (map-List (map-Arg (liftFrom i)) args)
liftFrom i (lam v t) = lam v (map-Abs (liftFrom (suc i)) t)
liftFrom i (pat-lam cs args) = unknown
liftFrom i (pi a b) = pi (map-Arg (liftFrom i) a) (map-Abs (liftFrom (suc i)) b)
liftFrom i (agda-sort s) = agda-sort (liftFromSort i s)
liftFrom i (lit l) = lit l
liftFrom i (meta x y) = unknown
liftFrom i unknown = unknown

liftPat : Pattern -> Pattern
liftPat (var x) = var (suc x)
liftPat (con c ps) = (absurd 0)
liftPat (dot t) = absurd 0
liftPat (lit l) = lit l
liftPat (proj f) = absurd 0
liftPat (absurd _) = absurd 0

liftPats : List (Arg Pattern) -> List (Arg Pattern)
liftPats = map-List (map-Arg liftPat)


-- === Unbound lifiting of many

-- lowerAbove : β -> β -> β
-- lowerAbove i j with i β€? j
-- ... | false = j
-- lowerAbove i zero | true = zero
-- lowerAbove i (suc j) | true = j

liftMany : β -> Type -> Type

{-# TERMINATING #-}
liftManyVar : β -> β Γ List (Arg Term) -> β Γ List (Arg Term)
liftManyVar i (j , ts) = i +-β j , map-List (map-Arg (liftMany i)) ts

liftManySort : β -> Sort -> Sort
liftManySort i (set t) = set (liftMany i t)
liftManySort i (lit n) = lit n
liftManySort i unknown = unknown
liftManySort i (prop t) = prop (liftMany i t)
liftManySort i (propLit n) = propLit n
liftManySort i (inf n) = inf n

liftMany i (var x args) = let (x , args) = liftManyVar i (x , args) in var x args
liftMany i (con c args) = con c (map-List (map-Arg (liftMany i)) args)
liftMany i (def f args) = def f (map-List (map-Arg (liftMany i)) args)
liftMany i (lam v t) = lam v (map-Abs (liftMany (i)) t)
liftMany i (pat-lam cs args) = unknown
liftMany i (pi a b) = pi (map-Arg (liftMany i) a) (map-Abs (liftMany (i)) b)
liftMany i (agda-sort s) = agda-sort (liftManySort i s)
liftMany i (lit l) = lit l
liftMany i (meta x y) = unknown
liftMany i unknown = unknown

--

first : {A B C : π° π} -> (A -> C) -> (A Γ B) -> (C Γ B)
first f (a , b) = f a , b

second : {A B C : π° π} -> (B -> C) -> (A Γ B) -> (A Γ C)
second f (a , b) = a , f b

insertList : β{A : π° π} -> β -> A -> List A -> List A
insertList zero a xs = a β· xs
insertList (suc i) a [] = []
insertList (suc i) a (x β· xs) = x β· insertList i a xs

liftTCMaybe : β{A : π° π} -> Maybe A -> String -> TC A
liftTCMaybe (left x) s = printErr s
liftTCMaybe (just x) s = return x

Ξ· : β{A : π° π} -> A -> List A
Ξ· a = a β· []

ΞΌ : β{A : π° π} -> List (List A) -> List A
ΞΌ [] = []
ΞΌ (a β· as) = a <> ΞΌ as


-- == getting (free?) variables

lowerVars : List β -> List β
lowerVars [] = []
lowerVars (zero β· xs) = lowerVars xs
lowerVars (suc x β· xs) = x β· lowerVars xs


{-# TERMINATING #-}
getVars : Visibility -> Type -> List β

getVarsArg : Visibility -> Arg Term -> List β
getVarsArg v (arg (arg-info w _) x) with v β w
... | true = getVars v x
... | false = []

getVarsSort : Visibility -> Sort -> List β
getVarsSort v (set t) = getVars v t
getVarsSort v (lit n) = []
getVarsSort v unknown = []
getVarsSort v (prop t) = getVars v t
getVarsSort v (propLit n) = []
getVarsSort v (inf n) = []

getVars v (var x args) = Ξ· x <> ΞΌ (map-List (getVarsArg v) args)
getVars v (con c args) = ΞΌ (map-List (getVarsArg v) args)
getVars v (def f args) = ΞΌ (map-List (getVarsArg v) args)
getVars v (lam Ο t) = []
getVars v (pat-lam cs args) = []
getVars v (pi (arg i x) (Abs.abs _ b)) = getVars v x <> (lowerVars (getVars v b))
getVars v (agda-sort s) = getVarsSort v s
getVars v (lit l) = []
getVars v (meta x xβ) = []
getVars v unknown = []

-- == replacing

SSub = β Γ (List (Arg Term) -> Type)

jumpOverAbs : SSub -> SSub
jumpOverAbs (i , Ο) = (suc i , (Ξ» args -> liftMany 1 (Ο args)))

-- replaceNat : SSub -> β -> Type

replace : SSub -> Type -> Type

{-# TERMINATING #-}
replaceVar : SSub -> β Γ List (Arg Term) -> Term
replaceVar (i , Ο) (j , args) with i β-β j
... | eq _ = Ο (map-List (map-Arg (replace (i , Ο))) args)
... | _ = var j (map-List (map-Arg (replace (i , Ο))) args)
-- replaceVar i (j , ts) = {!!} -- replaceNat i j , map-List (map-Arg (replace i)) ts

replaceSort : SSub -> Sort -> Sort
replaceSort i (set t) = set (replace i t)
replaceSort i (lit n) = lit n
replaceSort i unknown = unknown
replaceSort i (prop t) = prop (replace i t)
replaceSort i (propLit n) = propLit n
replaceSort i (inf n) = inf n

replace i (var x args) = replaceVar i (x , args)
replace i (con c args) = con c (map-List (map-Arg (replace i)) args)
replace i (def f args) = def f (map-List (map-Arg (replace i)) args)
replace i (lam v t) = lam v (map-Abs (replace (jumpOverAbs i)) t)
replace i (pat-lam cs args) = unknown
replace i (pi a b) = pi (map-Arg (replace i) a) (map-Abs (replace (jumpOverAbs i)) b)
replace i (agda-sort s) = agda-sort (replaceSort i s)
replace i (lit l) = lit l
replace i (meta x y) = unknown
replace i unknown = unknown


-- == substituting


tesubst : SSub -> Type -> Type


{-# TERMINATING #-}
tesubstVar : SSub -> β Γ List (Arg Term) -> Term
tesubstVar (i , Ο) (j , args) with i β-β j
... | eq _ = Ο (map-List (map-Arg (tesubst (i , Ο))) args)
... | gt _ = var j (map-List (map-Arg (tesubst (i , Ο))) args)
... | lt p = var (predβ j) (map-List (map-Arg (tesubst (i , Ο))) args)
-- ... | _ = var j (map-List (map-Arg (tesubst (i , Ο))) args)
-- tesubstVar i (j , ts) = {!!} -- tesubstNat i j , map-List (map-Arg (tesubst i)) ts

tesubstSort : SSub -> Sort -> Sort
tesubstSort i (set t) = set (tesubst i t)
tesubstSort i (lit n) = lit n
tesubstSort i unknown = unknown
tesubstSort i (prop t) = prop (tesubst i t)
tesubstSort i (propLit n) = propLit n
tesubstSort i (inf n) = inf n

tesubst i (var x args) = tesubstVar i (x , args)
tesubst i (con c args) = con c (map-List (map-Arg (tesubst i)) args)
tesubst i (def f args) = def f (map-List (map-Arg (tesubst i)) args)
tesubst i (lam v t) = lam v (map-Abs (tesubst (jumpOverAbs i)) t)
tesubst i (pat-lam cs args) = unknown
tesubst i (pi a b) = pi (map-Arg (tesubst i) a) (map-Abs (tesubst (jumpOverAbs i)) b)
tesubst i (agda-sort s) = agda-sort (tesubstSort i s)
tesubst i (lit l) = lit l
tesubst i (meta x y) = unknown
tesubst i unknown = unknown



