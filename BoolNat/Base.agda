-- This module defines an extension to the boolean expression language. Now unary natural numbers are introduced, 
-- along with  a predicate to check whether a number is zero. This language is typed: terms can either represent a 
-- boolean or a number.
-- Small-step and big-step semantics are also defined for this language and the soundness and completeness thereof are 
-- proven.

module Base where

------------------------------------------------------------------------
-- Prelude.

open import Data.Nat
open import Data.Unit
open import Data.Product
open import Data.Sum
open import Data.Empty
open import Data.Maybe
open import Data.Fin using (Fin; fromℕ; toℕ)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
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
 num           : ℕ -> Term Natural
 iszero        : Term Natural -> Term Boolean
 if_then_else_ : forall {ty} -> (cond  : Term Boolean)
                             -> (tcase : Term ty)
                             -> (fcase : Term ty)
                             -> Term ty
 new           : forall {ty} -> Term ty -> Term (Ref ty)
 !_            : forall {ty} -> Term (Ref ty) -> Term ty
 _<-_          : forall {ty} -> Term (Ref ty) -> Term ty -> Term ty
 ref           : forall {ty} -> ℕ -> Term (Ref ty)  -- References are indexes
 try_catch_    : forall {ty} -> Term ty -> Term ty -> Term ty
 -- raise         : forall {ty} Term ty -> Term ty -- This allows to return a value with the exception ( I don't know if we want it right now, maybe later)

--------------------------------------------------------------------------------
-- Values
--------------------------------------------------------------------------------

data Value : Type -> Set where
  vtrue vfalse : Value Boolean
  vnat : ℕ -> Value Natural
  vref : ∀ {ty} -> ℕ -> Value (Ref ty)
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
data Heap : ℕ -> Set where
  Nil : Heap 0
  Cons : forall {ty n} -> (v : Value ty) -> Heap n -> Heap (1 + n)

-- Partial lookup in the heap.
-- If the index given is correct and the required type match with the stored value type, the value is returned.
-- Otherwise verror is returned.
lookup : ∀ {ty n} -> (m : ℕ)  -> Heap n -> Value ty
lookup m Nil = verror
lookup {ty} zero (Cons {ty'} v H) with ty =? ty' 
lookup zero (Cons v H)  | just refl = v
lookup zero (Cons v H) | nothing = verror
lookup (suc m) (Cons v H) = lookup m H


-- Safe lookup for type. Returns the type of the value at the given position
lookupTy : ∀ {n} -> (H : Heap n) -> (fn : Fin n) -> Type
lookupTy (Cons {ty} v H) Data.Fin.zero = ty
lookupTy (Cons v H) (Data.Fin.suc f) = lookupTy H f


data Elem : ∀ {n} -> Heap n -> ℕ -> Type -> Set where
  Top : ∀ {n ty} {v : Value ty} {H : Heap n} -> Elem (Cons v H) 0 ty
  Pop : ∀ {n ty i ty'} {v : Value ty'} {H : Heap n} -> (Elem H i ty) -> Elem (Cons v H) (suc i) ty


tyEq : (ty1 ty2 : Type) -> (ty1 ≡ ty2) ⊎ (ty1 ≢ ty2)
tyEq Boolean Boolean = inj₁ refl
tyEq Boolean Natural = inj₂ (λ ())
tyEq Boolean (Ref ty2) = inj₂ (λ ())
tyEq Natural Boolean = inj₂ (λ ())
tyEq Natural Natural = inj₁ refl
tyEq Natural (Ref ty2) = inj₂ (λ ())
tyEq (Ref ty1) Boolean = inj₂ (λ ())
tyEq (Ref ty1) Natural = inj₂ (λ ())
tyEq (Ref ty1) (Ref ty2) with tyEq ty1 ty2
tyEq (Ref .ty2) (Ref ty2) | inj₁ refl = inj₁ refl
tyEq (Ref ty1) (Ref ty2) | inj₂ y = inj₂ (λ x → y (f x))
  where f : ∀ {ty3 ty4} -> (Ref ty3 ≡ Ref ty4) -> ty3 ≡ ty4
        f refl = refl


elem-eq : ∀ {n ty ty₁} {H : Heap n} {v : Value ty} -> (e : Elem (Cons v H) 0 ty₁) -> (ty₁ ≡ ty)
elem-eq Top = refl


elem-suc : ∀ {n i ty ty2} {H : Heap n} {v : Value ty2} -> (Elem (Cons v H) (suc i) ty) -> Elem H i ty
elem-suc (Pop e) = e

elem? : ∀ {n} -> (H : Heap n) -> (fn : ℕ) -> (ty : Type) -> ((Elem {n} H fn ty) ⊎ (¬ (Elem {n} H fn ty)))
elem? Nil i ty = inj₂ g
  where g : ∀ {ty i} -> Elem Nil i ty -> ⊥
        g ()
elem? (Cons {ty} v H) zero ty₁ with tyEq ty₁ ty
elem? (Cons {ty} v H) zero .ty | inj₁ refl = inj₁ Top
elem? (Cons {ty} v H) zero ty₁ | inj₂ y = inj₂ (λ x → y (elem-eq x))
elem? (Cons v H) (suc n₁) ty₁ with elem? H n₁ ty₁
elem? (Cons v H) (suc n₁) ty₁ | inj₁ x = inj₁ (Pop x)
elem? (Cons v H) (suc n₁) ty₁ | inj₂ y = inj₂ (λ x → y (elem-suc x))


replace : ∀ {ty n} -> {fn : ℕ} -> (H : Heap n) -> Elem H fn ty -> Value ty -> Heap n
replace .(Cons v H) (Top {n} {ty} {v} {H}) v₁ = Cons v₁ H
replace .(Cons v H) (Pop {n} {ty} {i} {ty'} {v} {H} e) v₁ = Cons v (replace H e v₁)
