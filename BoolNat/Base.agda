-- This module defines an extension to the boolean expression language. Now unary natural numbers are introduced, 
-- along with  a predicate to check whether a number is zero. This language is typed: terms can either represent a 
-- boolean or a number.
-- Small-step and big-step semantics are also defined for this language and the soundness and completeness thereof are 
-- proven.

module Base where

------------------------------------------------------------------------
-- Prelude.

open import Data.Nat renaming (ℕ to Nat)
open import Data.Unit
open import Data.Product
open import Data.Empty
open import Data.Maybe
open import Data.Fin using (Fin; fromℕ)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Core

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
 num           : Nat -> Term Natural
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

isError : forall {ty} -> Term ty -> Set
isError error = Unit
isError _ = ⊥

isValue : forall {ty} -> Term ty -> Set
isValue true = Unit
isValue false = Unit
isValue error = Unit
isValue (num _) = Unit
isValue (ref _) = Unit
isValue (iszero t) = ⊥
isValue (if t then t₁ else t₂) = ⊥
isValue (new t) = ⊥
isValue (!_ t) = ⊥
isValue (_<-_ t t₁) = ⊥
isValue (try t catch t') = ⊥

isGoodValue : ∀ {ty} -> Term ty -> Set
isGoodValue t = (isValue t) × (¬ isError t)


-- Maps an already evaluated term in the value world (does not use ⟦ _ ⟧)
⌞_,_⌟ : ∀ {ty} -> (t : Term ty) -> isValue t -> Value ty
⌞_,_⌟ true v = vtrue
⌞_,_⌟ false v = vfalse
⌞_,_⌟ (num n) v = vnat n
⌞_,_⌟ (iszero t) ()
⌞_,_⌟ (if t then t₁ else t₂) ()
⌞_,_⌟ (new t) ()
⌞_,_⌟ (! t) ()
⌞_,_⌟ (t <- t₁) ()
⌞_,_⌟ (ref x) v = vref x
⌞_,_⌟ error v = verror 
⌞_,_⌟ (try t catch t') () 


-- Maps a value back in the term world
⌜_⌝ : ∀ {ty} -> Value ty -> Term ty
⌜ vtrue ⌝ = true
⌜ vfalse ⌝ = false
⌜ verror ⌝ = error
⌜ vref x ⌝ = ref x
⌜ vnat n ⌝ = num n

-- View function for isValue. 
isValue? : ∀ {ty} -> (v : Value ty) -> isValue ⌜ v ⌝
isValue? vtrue = unit
isValue? vfalse = unit
isValue? (vnat zero) = unit
isValue? (vnat (suc n)) = isValue? (vnat n) 
isValue? (vref x) = unit
isValue? verror = unit
  
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

-- Proof object that guarantees the safeness of replace.
data Replace : ∀ {n} -> Heap n -> Type -> Set where
  -- TODO maybe the contstraint over the same type should be put back, otherwise you could construct your proof
  -- yourself, without using replace? .
  RepN : ∀ {n ty} {H : Heap n} -> (fn : Fin n) -> Replace H ty  

-- View function for Replace
replace? : ∀ {n} -> (H : Heap n) -> Nat -> (ty : Type) -> Maybe (Replace H ty)
replace? Nil m ty = nothing
replace? (Cons {ty'} v H) zero ty with ty =? ty'
replace? (Cons {ty} v H) zero .ty | just refl = just (RepN Data.Fin.zero)
replace? (Cons v H) zero ty₁ | nothing = nothing  -- The type of a cell cannot change
replace? (Cons v H) (suc m) ty with replace? H m ty
replace? (Cons v H) (suc m) ty | just (RepN fn) = just (RepN (Data.Fin.suc fn))
replace? (Cons v H) (suc m) ty | nothing = nothing

-- Safe replace. Replaces the value at the given position with another value of the same type.
replace : ∀ {ty n} -> Value ty -> (H : Heap n) -> Replace H ty -> Heap n
replace v (Cons v₁ H) (RepN Data.Fin.zero) = Cons v H
replace v (Cons v₁ H) (RepN (Data.Fin.suc fn)) = Cons v₁ (replace v H (RepN fn))
