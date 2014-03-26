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
 ref           : forall {ty} -> Term (Ref ty)
 
-- are refs values as well?
isValue : forall {ty} -> Term ty -> Set
isValue true = Unit
isValue false = Unit
isValue zero = Unit
isValue ref = Unit
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

-- xs ⊆ ys i.e. ∃ zs : xs ≡  zs ++ ys
data _⊆_ : Shape -> Shape -> Set where
  Same : ∀ {s} -> s ⊆ s
  Grow : ∀ {s1 s2 ty} -> s1 ⊆ s2 -> s1 ⊆ (Cons ty s2)

mutual
  data Δ : ∀ {S1 S2} -> S1 ⊆ S2 -> Heap S1 -> Heap S2 -> Set where
    Same : ∀ {S} -> (H : Heap S) -> Δ Same H H
    Allocate : ∀ {ty S1 S2} {s : S1 ⊆ S2} {H1 : Heap S1} {H2 : Heap S2} {v : Term ty} {isV : isValue v} ->
               Δ s H1 H2 -> Δ (Grow s) H1 (Cons v S2 isV H2)
    Replace : ∀ {ty S1 S2} {s : S1 ⊆ S2} {H1 : Heap S1} {H2 : Heap S2} (e : Elem S2 ty) (t : Term ty) {isV : isValue t} ->
              Δ s H1 H2 -> Δ s H1 (replace H2 e t isV)  

  replace : ∀ {ty S} -> Heap S -> Elem S ty -> (t : Term ty) -> isValue t -> Heap S
  replace (Cons x S isV xs) Top x' isV' = Cons x' S isV' xs
  replace (Cons x S isV xs) (Pop p) x' isV' = Cons x S isV (replace xs p x' isV')


-- If S' is a prefix of S an element of S' is also an element S
weaken : ∀ {ty S S'} -> S' ⊆ S -> Elem S' ty -> Elem S ty
weaken Same p = p
weaken (Grow isP) p = Pop (weaken isP p)

lookup : forall {ty S} -> Heap S -> Elem S ty -> Term ty
lookup (Cons x S isV xs) Top = x
lookup (Cons x S isV xs) (Pop p) = lookup xs p -- Note that due to ref you could also fill with ! ref p which does not make sense! 

data Closed : Type -> Set where
  Closure : forall {ty} -> Term ty -> Shape -> Closed ty
  CNew    : forall {ty} -> (S1 : Shape) -> Term ty -> (S2 : Shape) -> S1 ⊆ S2 -> Closed ty
  CAcc    : forall {ty} -> Closed ty

-- TODO: add something like isPrefix, proofing that the shape never shrinks
data Step : forall {ty S1 S2} -> {H1 : Heap S1} -> {H2 : Heap S2} -> {s : S1 ⊆ S2} -> Δ s H1 H2 -> Term ty -> Term ty -> Set where
 E-IfTrue     : ∀ {ty S} {H : Heap S} {t1 t2 : Term ty} -> Step (Same H) (if true  then t1 else t2) t1
 E-IfFalse    : ∀ {ty S} {H : Heap S} {t1 t2 : Term ty} -> Step (Same H) (if false then t1 else t2) t2
 E-If         : ∀ {ty S1 S2 t1 t1'} {s : S1 ⊆ S2} {H1 : Heap S1} {H2 : Heap S2} {δ : Δ s H1 H2} {t2 t3 : Term ty} ->
                Step δ t1 t1' -> Step δ (if t1 then t2 else t3) (if t1' then t2 else t3)
 E-Succ       : ∀ {S1 S2 t t'} {s : S1 ⊆ S2} {H1 : Heap S1} {H2 : Heap S2} {δ : Δ s H1 H2} -> 
                Step {Natural} δ t  t' -> Step δ (succ t) (succ t')
 E-IsZeroZero : ∀ {S} {H : Heap S} -> Step (Same H) (iszero zero) true
 E-IsZeroSucc : ∀ {S t} {H : Heap S} -> isValue t -> Step (Same H) (iszero (succ t)) false
 E-IsZero     : ∀ {S1 S2 t t'} {s : S1 ⊆ S2} {H1 : Heap S1} {H2 : Heap S2} {δ : Δ s H1 H2} ->
                Step δ t t' -> Step δ (iszero t) (iszero t')
 E-New        : ∀ {ty S1 S2 t t'} {s : S1 ⊆ S2} {H1 : Heap S1} {H2 : Heap S2} {δ : Δ s H1 H2} ->
                Step δ t t' -> Step {Ref ty} δ (new t) (new t')
 E-NewVal     : ∀ {ty S} {H : Heap S} {v : Term ty} {isV : isValue v} -> 
                Step (Allocate {v = v} {isV = isV} (Same H)) (new v) ref
 E-Deref      : ∀ {ty S1 S2 t t'} {s : S1 ⊆ S2} {H1 : Heap S1} {H2 : Heap S2} {δ : Δ s H1 H2} ->
                Step {Ref ty} δ t t' -> Step {ty} δ (! t) (! t')
 E-DerefVal   : forall {S S' H ty} {e : Elem S' ty} {isP : S' ⊆ S} {t : Term (Ref ty)} -> 
                Step {ty} (Same H) (! t) (lookup H (weaken isP e))
 E-AssLeft    : ∀ {ty S1 S2} {s : S1 ⊆ S2} {H1 : Heap S1} {H2 : Heap S2} {δ : Δ s H1 H2} {t1 t1' : Term (Ref ty)} {t2 : Term ty} ->
                Step {Ref ty} δ t1 t1' ->  Step {ty} δ (t1 <- t2) (t1' <- t2)
 E-AssRight   : ∀ {ty S1 S2} {s : S1 ⊆ S2} {H1 : Heap S1} {H2 : Heap S2} {δ : Δ s H1 H2} {v : Term (Ref ty)} {t t' : Term ty} 
                (isV : isValue v) -> Step δ t t' -> Step δ (v <- t) (v <- t')
 E-AssRed     : ∀ {ty S S'} {H : Heap S} {v1 : Term (Ref ty)} {v2 : Term ty} -> 
                {isV1 : isValue v1} {isV2 : isValue v2} {e : Elem S' ty} {isP : S' ⊆ S} ->
                Step (Replace (weaken isP e) v2 {isV2} (Same H)) (v1 <- v2) v2

-- You don't need this proof anymore, it's directly encoded in the Step
-- Proof that the shape only grows. Could be useful for proofs.
no-shrink :  ∀ {ty S1 S2} {H1 : Heap S1} {H2 : Heap S2} {s : S1 ⊆ S2} {t1 t2 : Term ty} {δ : Δ s H1 H2} 
             -> Step δ t1 t2 -> S1 ⊆ S2
no-shrink {s = s} stp = s

-- Sequences of small steps.

trans : ∀ {S1 S2 S3} -> S1 ⊆ S2 -> S2 ⊆ S3 -> S1 ⊆ S3
trans Same s2 = s2
trans (Grow s1) Same = Grow s1
trans (Grow s1) (Grow s2) = Grow (trans (Grow s1) s2)

-- Concatenates deltas
_<++>_ :  {S1 S2 S3 : Shape} {s1 : S1 ⊆ S2} {s2 : S2 ⊆ S3} {H1 : Heap S1} {H2 : Heap S2} {H3 : Heap S3} ->   
          Δ s1 H1 H2 -> Δ s2 H2 H3 -> Δ (trans s1 s2) H1 H3
(Same H2) <++> δ2 = δ2
Allocate {ty} {._} {S2} {s} {._} {H2} {v} {isV} δ1 <++> Same .(Cons v S2 isV H2) = Allocate δ1
Allocate δ1 <++> Allocate δ2 = Allocate (Allocate δ1 <++> δ2)
Allocate δ1 <++> Replace e t δ2 = Replace e t (Allocate δ1 <++> δ2) 
Replace {ty} {._} {._} {._} {._} {H2} e t {isV} δ1 <++> Same .(replace H2 e t isV) = Replace e t (δ1 <++> Same H2)
Replace e t δ1 <++> (Allocate δ2) = Replace e t δ1 <++> Allocate δ2
Replace e t δ1 <++> Replace e₁ t₁ δ2 = Replace e₁ t₁ (Replace e t δ1 <++> δ2)

-- -- A sequence of steps that can be applied in succession.
data Steps : forall {ty} -> {S1 S2 : Shape} -> {H1 : Heap S1} -> {H2 : Heap S2} -> {s : S1 ⊆ S2} -> Δ s H1 H2 -> Term ty -> Term ty -> Set where
  []  : ∀ {ty} {S : Shape} {H : Heap S} {t : Term ty} -> Steps (Same H) t t
  _::_ : ∀ {ty} {S1 S2 S3 : Shape} {s1 : S1 ⊆ S2} {s2 : S2 ⊆ S3} {H1 : Heap S1} {H2 : Heap S2} {H3 : Heap S3} 
           {δ1 : Δ s1 H1 H2} {δ2 : Δ s2 H2 H3} {t1 t2 t3 : Term ty} ->
           Step δ1 t1 t2 -> Steps δ2 t2 t3 -> Steps (δ1 <++> δ2) t1 t3

-- -- Single-step sequence.
-- [_] : forall {ty S1 S2 H1 H2} {t1 t2 : Term ty} -> Step {ty} {S1} {S2} {H1} {H2} t1 t2 -> Steps {ty} {S1} {S2} {H1} {H2} t1 t2
-- [_] x = x :: [] 
  
-- -- Concatenation.
-- _++_ : forall {ty S1 S2 S3} {H1 : Heap S1} {H2 : Heap S2} {H3 : Heap S3} {t1 t2 t3 : Term ty} -> 
--        Steps {ty} {S1} {S2} {H1} {H2} t1 t2 -> Steps {ty} {S2} {S3} {H2} {H3} t2 t3 -> Steps t1 t3
-- [] ++ ys = ys
-- (x :: xs) ++ ys = x :: (xs ++ ys)


-- -- Evidence type that shows a certain term represents a value.
-- data Is-value : {ty : Type} -> Term ty -> Set where
--   is-value : forall {ty} -> (v : Value ty) -> Is-value (val v)

-- ------------------------------------------------------------------------

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
