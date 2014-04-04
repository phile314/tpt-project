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
open import Data.Maybe
open import Data.Fin using (Fin)
open import Relation.Binary.PropositionalEquality

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

data Type : Set where
 Boolean : Type
 Natural : Type
 Ref : (ty : Type) -> Type

-- View function : are two types the same?
_=?_ : (ty : Type) -> (ty' : Type) -> Maybe (ty ≡ ty')
Boolean =? Boolean = just refl
Natural =? Natural = just refl
Ref ty1 =? Ref ty2 with ty1 =? ty2
Ref .ty2 =? Ref ty2 | just refl = just refl
Ref ty1 =? Ref ty2 | nothing = nothing
_ =? _ = nothing
 
--------------------------------------------------------------------------------
-- Terms and syntax and type rules.
--------------------------------------------------------------------------------

data Term : Type -> Set where
 true          : Term Boolean
 false         : Term Boolean
 error         : ∀ {ty} -> Term ty 
 zero          : Term Natural
 succ          : Term Natural -> Term Natural
 iszero        : Term Natural -> Term Boolean
 if_then_else_ : forall {ty} -> (cond  : Term Boolean)
                             -> (tcase : Term ty)
                             -> (fcase : Term ty)
                             -> Term ty
 new           : forall {ty} -> Term ty -> Term (Ref ty)
 !_            : forall {ty} -> Term (Ref ty) -> Term ty
 _<-_          : forall {ty} -> Term (Ref ty) -> Term ty -> Term ty
 ref           : forall {ty} -> Nat -> Term (Ref ty)  -- References are indexes
 try_catch_    : forall {ty} -> Term ty -> Term ty -> Term ty
 -- raise         : forall {ty} Term ty -> Term ty -- This allows to return a value with the exception ( I don't know if we want it right now, maybe later)

--------------------------------------------------------------------------------
-- Values
--------------------------------------------------------------------------------

data Value : Type -> Set where
  vtrue vfalse : Value Boolean
  vnat : Nat -> Value Natural
  vref : ∀ {ty} -> Nat -> Value (Ref ty)
  verror : ∀ {ty} -> Value ty 

isValue : forall {ty} -> Term ty -> Set
isValue true = Unit
isValue false = Unit
isValue zero = Unit
isValue error = Unit
isValue (ref _) = Unit
isValue (succ t) = isValue t
isValue (iszero t) = ⊥
isValue (if t then t₁ else t₂) = ⊥
isValue (new t) = ⊥
isValue (!_ t) = ⊥
isValue (_<-_ t t₁) = ⊥
isValue (try t catch t') = ⊥

-- Maps a value back in the term world
⌜_⌝ : ∀ {ty} -> Value ty -> Term ty
⌜ vtrue ⌝ = true
⌜ vfalse ⌝ = false
⌜ verror ⌝ = error
⌜ vnat zero ⌝ = zero
⌜ vnat (suc n) ⌝ = succ ⌜ vnat n ⌝
⌜ vref x ⌝ = ref x

--------------------------------------------------------------------------------
-- Heap
--------------------------------------------------------------------------------

-- Vector of values
data Heap : Nat -> Set where
  Nil : Heap 0
  Cons : forall {ty n} -> (v : Value ty) -> Heap n -> Heap (1 + n)

-- Partial lookup in the heap.
-- If the index given is correct and the required type match with the stored value type, the value is returned.
-- Otherwise verror is returned.
lookup : ∀ {ty n} -> (m : Nat)  -> Heap n -> Value ty
lookup m Nil = verror
lookup {ty} zero (Cons {ty'} v H) with ty =? ty' 
lookup zero (Cons v H)  | just refl = v
lookup zero (Cons v H) | nothing = verror
lookup (suc m) (Cons v H) = lookup m H

-- Safe lookup for type. Returns the type of the value at the given position
lookupTy : {n : Nat} -> Fin n -> Heap n -> Type
lookupTy Data.Fin.zero (Cons {ty} v H) = ty
lookupTy (Data.Fin.suc fn) (Cons v H) = lookupTy fn H

-- Safe replace. Replaces the value at the given position with another value of the same type.
replace : ∀ {ty n} -> Value ty -> (fn : Fin n) -> (H : Heap n) -> (ty ≡ lookupTy fn H) -> Heap n
replace v Data.Fin.zero (Cons v' H) refl = Cons v H
replace v (Data.Fin.suc fn) (Cons v' H) p = Cons v' (replace v fn H p)
