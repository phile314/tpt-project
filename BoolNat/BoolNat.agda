-- This module defines an extension to the boolean expression language. Now unary natural numbers are introduced, 
-- along with  a predicate to check whether a number is zero. This language is typed: terms can either represent a 
-- boolean or a number.
-- Small-step and big-step semantics are also defined for this language and the soundness and completeness thereof are 
-- proven.
module BoolNat where

------------------------------------------------------------------------
-- Prelude.

open import Data.Nat renaming (ℕ to Nat)
open import Data.Unit
open import Data.Empty
------------------------------------------------------------------------
-- Syntax.

-- The type system of the language consists of booleans and natural numbers.
data Type : Set where
 Boolean : Type
 Natural : Type
 Ref : (ty : Type) -> Type

data Shape : Set where
  Nil : Shape
  Cons : Type -> Shape -> Shape

data Elem : Shape -> Type -> Set where
  Top : forall {S ty} -> Elem (Cons ty S) ty
  Pop : forall {S ty a} -> Elem S ty -> Elem (Cons a S) ty
 
-- The grammar of the language. A natural number n is represented as a succession of n succ operators applied to the 
-- constant zero.
data Term : Type -> Set where
 true          : Term Boolean
 false         : Term Boolean
 zero          : Term Natural
 succ          : Term Natural -> Term Natural
 iszero        : Term Natural -> Term Boolean
 if_then_else_ : forall {ty} -> (cond  : Term Boolean)
                             -> (tcase : Term ty)
                             -> (fcase : Term ty)
                             -> Term ty
 new           : forall {ty} -> Term ty -> Term (Ref ty)
 !_            : forall {ty} -> Term (Ref ty) -> Term ty
 _:=_          : forall {ty} -> Term (Ref ty) -> Term (Ref ty) -> Term (Ref ty)
 _<-_          : forall {ty} -> Term (Ref ty) -> Term ty -> Term ty
 ref           : forall {S ty} -> Elem S ty -> Term (Ref ty) -- this doesn't actually contain the pointer/elem proof at the moment. maybe extend later.
 
-- are refs values as well?
isValue : forall {ty} -> Term ty -> Set
isValue true = Unit
isValue false = Unit
isValue zero = Unit
isValue (ref _) = Unit
isValue (succ t) = isValue t
isValue (iszero t) = ⊥
isValue (if t then t₁ else t₂) = ⊥
isValue (new t) = ⊥
isValue (!_ t) = ⊥
isValue (t := t₁) = ⊥
isValue (_<-_ t t₁) = ⊥


data Heap : Shape -> Set where
  Nil : Heap Nil
  Cons : forall {ty} -> (t : Term ty) -> (s : Shape) -> isValue t -> Heap s -> Heap (Cons ty s)

data IsPrefix : Shape -> Shape -> Set where
-- TODO

lookup : forall {ty} -> {S S' : Shape} -> (Heap S) -> (isP : IsPrefix S' S) -> (e : Elem S' ty) -> Term ty
lookup h isp e = {!!} -- we need the IsPrefix proof now
--lookup Nil ()
--lookup (Cons t s x hs) Top = t
--lookup (Cons t s x hs) (Pop e) = lookup hs e

replace : forall {ty} -> {S : Shape} -> Heap S -> Elem S ty -> (t : Term ty) -> isValue t -> Heap S
replace Nil () t _
replace (Cons t s x h) Top t₁ iv = Cons t₁ s iv h
replace (Cons t s x h) (Pop e) t₁ iv = Cons t s x (replace h e t₁ iv)


data Closed : Type -> Set where
  Closure : forall {ty} -> Term ty -> Shape -> Closed ty
  CNew    : forall {ty} -> (S1 : Shape) -> Term ty -> (S2 : Shape) -> IsPrefix S1 S2 -> Closed ty
  CAcc    : forall {ty} -> Closed ty

-- TODO: add something like isPrefix, proofing that the shape never shrinks
data Step : forall {ty} -> {S1 S2 : Shape} -> {H1 : Heap S1} -> {H2 : Heap S2} -> Term ty -> Term ty -> Set where
 E-IfTrue     : forall {S1 S2 H1 H2} -> {ty : Type} -> {t1 t2 : Term ty} -> Step {ty} {S1} {S2} {H1} {H2} (if true  then t1 else t2)  t1
 E-IfFalse    : forall {S1 S2 H1 H2} -> {ty : Type} -> {t1 t2 : Term ty} -> Step {ty} {S1} {S2} {H1} {H2} (if false then t1 else t2)  t2
 E-If         : forall {S1 S2 H1 H2} -> {ty : Type} -> {t1 t1' : Term Boolean} -> {t2 t3 : Term ty} ->
                Step {Boolean} {S1} {S2} {H1} {H2} t1 t1' ->
                Step {ty} {S1} {S2} {H1} {H2} (if t1 then t2 else t3) (if t1' then t2 else t3)
 E-Succ       : forall {S1 S2 H1 H2 t t'} -> Step {Natural} {S1} {S2} {H1} {H2} t  t' -> Step {Natural} {S1} {S2} {H1} {H2} (succ t) (succ t')
 E-IsZeroZero : Step (iszero zero) true
-- E-IsZeroSucc : forall {v} -> Step (iszero (succ (val v))) false 
 E-IsZero     : forall {t t'} -> Step t t' -> Step (iszero t) (iszero t')
 E-New        : forall {S1 S2 H1 H2 ty t t'} -> Step {ty} {S1} {S2} {H1} {H2} t t' -> Step {Ref ty} {S1} {S2} {H1} {H2} (new t) (new t')
 E-NewVal     : forall {S1 H1 ty v} -> {isV : isValue v} -> Step {Ref ty} {S1} {Cons ty S1} {H1} {Cons v S1 isV H1} (new v) (ref (Top {Cons ty S1}))
 E-Deref      : forall {S1 S2 H1 H2 ty t t'} -> {E : Elem S2 ty} -> Step {Ref ty} {S1} {S2} {H1} {H2} t t' -> Step {ty} {S1} {S2} {H1} {H2} (! t) (! t')
 E-DerefVal   : forall {S S' H ty} -> {e : Elem S' ty} -> (isP : IsPrefix S' S) -> Step {ty} {S} {S} {H} {H} (! (ref {S'} e)) (lookup H isP e)
                -- the E-DerefVal only works if the value is a (ref ..). The isValue ensures that, but agda cannot immediately see that. Instead we now directly
                -- ensure that the term is a value by using (ref ...) directly in the first Term argument of Step.

-- -- Example term.
-- ex : Term Natural
-- ex = if true then zero else succ zero

-- -- The values of the language are true, false and all natural numbers.
-- data Value : Type -> Set where
--  trueV falseV : Value Boolean
--  natV         : Nat -> Value Natural

-- -- Obtain the term representing a certain natural.
-- natTerm : Nat -> Term Natural
-- natTerm Z = zero
-- natTerm (S n) = succ (natTerm n)

-- -- Convert a value to the corresponding term.
-- val : forall {ty} -> Value ty -> Term ty
-- val trueV = true
-- val falseV = false
-- val (natV x) = natTerm x

----------------------------------------------------------------------
-- Small-step semantics.

-- data Step : forall {ty} -> Term ty -> Term ty -> Set where
--  E-IfTrue     : {ty : Type} -> {t1 t2 : Term ty} -> Step (if true  then t1 else t2)  t1
--  E-IfFalse    : {ty : Type} -> {t1 t2 : Term ty} -> Step (if false then t1 else t2)  t2
--  E-If         : {ty : Type} -> {t1 t1' : Term Boolean} -> {t2 t3 : Term ty} ->
--                 Step t1 t1' ->
--                 Step (if t1 then t2 else t3) (if t1' then t2 else t3)
--  E-Succ       : forall {t t'} -> Step t  t' -> Step (succ t) (succ t')
--  E-IsZeroZero : Step (iszero zero) true
--  E-IsZeroSucc : forall {v} -> Step (iszero (succ (val v))) false 
--  E-IsZero     : forall {t t'} -> Step t t' -> Step (iszero t) (iszero t')


-- -- The example can be evaluated to zero.
-- exStep : Step ex zero
-- exStep = E-IfTrue

-- -- Evidence type that shows a certain term represents a value.
-- data Is-value : {ty : Type} -> Term ty -> Set where
--   is-value : forall {ty} -> (v : Value ty) -> Is-value (val v)

-- ------------------------------------------------------------------------
-- -- Sequences of small steps.

-- -- A sequence of steps that can be applied in succession.
-- data Steps : forall {ty} -> Term ty -> Term ty -> Set where
--   []  : forall {ty} {t : Term ty} -> Steps t t
--   _::_ : forall {ty} {t1 t2 t3 : Term ty} -> Step t1 t2 -> Steps t2 t3 -> Steps t1 t3

-- -- Single-step sequence.
-- [_] : forall {ty} {t1 t2 : Term ty} -> Step t1 t2 -> Steps t1 t2
-- [_] x = x :: [] 
  
-- -- Concatenation.
-- _++_ : forall {ty} {t1 t2 t3 : Term ty} -> Steps t1 t2 -> Steps t2 t3 -> Steps t1 t3
-- [] ++ ys = ys
-- (x :: xs) ++ ys = x :: (xs ++ ys)

-- -- An extension of the E-If rule, for multiple steps.
-- E-If* : forall {ty} {t1 t1′ : Term Boolean} {t2 t3 : Term ty} ->
--         Steps t1  t1′ ->
--         Steps (if t1 then t2 else t3) (if t1′ then t2 else t3)
-- E-If* [] = []
-- E-If* (x :: xs) = E-If x :: E-If* xs

-- -- Extending the E-Succ rule in the same manner.
-- E-Succ* : forall {t1 t2} -> Steps t1 t2 -> Steps (succ t1) (succ t2)
-- E-Succ* [] = []
-- E-Succ* (x :: xs) = E-Succ x :: E-Succ* xs

-- -- E-IsZero rules for multiple steps.
-- E-IsZero* : forall {t1 t2} -> Steps t1 t2 -> Steps (iszero t1) (iszero t2)
-- E-IsZero* [] = []
-- E-IsZero* (x :: xs) = E-IsZero x :: E-IsZero* xs

-- E-IsZeroZero* : {t : Term Natural} -> Steps t (val (natV 0)) -> Steps (iszero t) (val trueV)
-- E-IsZeroZero* [] = E-IsZeroZero :: []
-- E-IsZeroZero* (x :: xs) = E-IsZero x :: E-IsZeroZero* xs

-- E-IsZeroSucc* : forall {n} {t : Term Natural} -> Steps t (val (natV (S n))) -> Steps (iszero t) (val falseV)
-- E-IsZeroSucc* {n} {.(succ (natTerm n))} [] = E-IsZeroSucc {natV n} :: []
-- E-IsZeroSucc* (x :: ts) = E-IsZero x :: E-IsZeroSucc* ts


-- -- A term can not evaluate to more than one value.


-- ------------------------------------------------------------------------
-- -- Expressing and proving termination.

-- -- The execution of a term terminates when there exists a step sequence that evaluates this term to a value.
-- data _=> {ty : Type} (t : Term ty) : Set where
--   terminates : forall v -> Steps t (val v) -> t =>

-- -- If t1 evaluates to t2, and t2 terminates, then t1 terminates as well.
-- prepend-steps : forall {ty} {t1 t2 : Term ty} -> Steps t1 t2  ->  t2 => ->  t1 =>
-- prepend-steps e (terminates v x) = terminates v (e ++ x)

-- -- All steps terminate.
-- termination : forall {ty} -> (t : Term ty) -> t =>
-- termination {.Boolean} true = terminates trueV []
-- termination false = terminates falseV []
-- termination zero = terminates (natV Z) []
-- termination (succ t) with termination t
-- termination (succ t) | terminates (natV k) x = terminates (natV (S k)) (E-Succ* x)
-- termination (iszero t) = {!!}
-- termination (if t then t₁ else t₂) = {!!}


-- ------------------------------------------------------------------------
-- -- Big-step semantics.

-- -- A different kind of representation for evaluation rules. 'a ⇓ b' denotes that a will evaluate to value b after a 
-- -- complete execution of the term.
-- data _=>_ : forall {ty} -> Term ty -> Value ty -> Set where
--  =>-True       : true  => trueV
--  =>-False      : false => falseV
--  =>-Zero       : zero  => natV 0
--  =>-IfTrue     : forall {ty} {t : Term Boolean} {t1 t2 : Term ty} {v : Value ty} ->
--                  t => trueV -> t1 => v ->
--                  if t then t1 else t2 => v
--  =>-IfFalse    : forall {ty} {t : Term Boolean} {t1 t2 : Term ty} {v : Value ty} ->
--                  t => falseV -> t2 => v ->
--                  if t then t1 else t2 => v
              
-- -- Converstion from big- to small-step representations.
-- big-to-small : forall {ty} {t : Term ty} {v : Value ty} -> t => v -> Steps t (val v)
-- big-to-small = {!!}

-- -- A value term evaluates to itself.
-- value-of-value : forall {ty} -> (v : Value ty) -> (val v) => v
-- value-of-value = {!!}

-- -- Combining a single small step with a big step.
-- prepend-step : forall {ty} {t1 t2 : Term ty} {v : Value ty} -> Step t1 t2 -> t2 => v -> t1 => v
-- prepend-step stp bstp = {!!}

-- -- Conversion from small- to big-step representations.
-- small-to-big : forall {ty} {t : Term ty} {v : Value ty} -> Steps t (val v) -> t => v
-- small-to-big = {!!}

-- ------------------------------------------------------------------------
-- -- Denotational semantics.

-- -- Evaluation of if-then-else expressions applied to values.
-- [if_then_else_]V : forall {ty} -> Value Boolean -> Value ty -> Value ty -> Value ty
-- [if trueV  then v1 else v2 ]V = v1
-- [if falseV then v1 else v2 ]V = v2

-- -- Evaluation function.
-- [[_]] : forall {ty} -> Term ty -> Value ty
-- [[ true ]] = trueV
-- [[ false ]] = falseV
-- [[ zero ]] = natV Z
-- [[ succ t ]] = {!!}
-- [[ iszero t ]] with [[ t ]]
-- [[ iszero t ]] | natV Z = trueV
-- [[ iszero t ]] | natV (S x) = falseV
-- [[ if t then t₁ else t₂ ]] = [if [[ t ]] then [[ t₁ ]] else [[ t₂ ]] ]V

-- -- Prove completeness of the big-step semantics when using the evaluation function: each term should reduce to its
-- -- evaluation.
-- =>-complete : forall {ty} -> (t : Term ty) -> t => [[ t ]]
-- =>-complete = {!!}

-- -- Prove soundness of the big-step semantics: when a term can be big-step evaluated to a value, this value should be
-- -- the evaluation of that term.
-- =>-sound : forall {ty} (t : Term ty) (v : Value ty) -> t => v -> v == [[ t ]]
-- =>-sound = {!!}

-- --------------------------------------------------------------------------------

-- -- Progress and preservation
-- progress : {ty : Type} -> (t : Term ty) -> Either (Is-value t) (Exists (Term ty) (Step t))
-- progress true = left (is-value trueV)
-- progress false = left (is-value falseV)
-- progress zero = left (is-value (natV Z))
-- progress (succ t) with progress t
-- progress (succ .(val v)) | left (is-value v) = left (is-value (natV (S {!natTerm v!})))
-- progress (succ t) | right ( t' , step ) = right (succ t' , E-Succ step )
-- progress (iszero t) with progress t
-- progress (iszero .zero) | left (is-value (natV Z)) = right (_ , E-IsZeroZero)
-- progress (iszero .(succ (natTerm x))) | left (is-value (natV (S x))) = right ( {!!})
-- progress (iszero t) | right (t' , step) = right {!!}
-- progress (if t then t₁ else t₂) = {!!}

-- preservation : {ty ty' : Type} {t : Term ty} {t' : Term ty} -> Step t t' -> ty == ty
-- preservation t = refl
