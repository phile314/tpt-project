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
open import Relation.Binary.PreorderReasoning

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
 _>>_           : ∀ {ty1 ty2} -> Term ty1 -> Term ty2 -> Term ty2 -- sequencing

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

-- Equivalent on the value level
isVError : ∀ {ty} -> Value ty -> Set
isVError verror = Unit
isVError _ = ⊥

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
isValue (_ >> _) = ⊥

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
⌞ try t catch t' , () ⌟
⌞ t >> t' , () ⌟


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
  Cons : forall {ty} {n : ℕ} -> (v : Value ty) -> Heap n -> Heap (1 + n)



-- Partial lookup in the heap.
-- If the index given is correct and the required type match with the stored value type, the value is returned.
-- Otherwise verror is returned.
lookup : ∀ {ty n} -> (m : ℕ)  -> Heap n -> Value ty
lookup m Nil = verror
lookup m (Cons {_} {n} v H) with compare m n
lookup m (Cons v H) | less .m k = lookup m H
lookup {ty} .n (Cons {ty₁} {n} v H) | equal .n with ty =? ty₁
lookup .n (Cons {ty} {n} v H) | equal .n | just refl = v
lookup .n (Cons {ty₁} {n} v H) | equal .n | nothing = verror
lookup .(suc (n + k)) (Cons {ty₁} {n} v H) | greater .n k = verror



-- Safe lookup for type. Returns the type of the value at the given position
-- lookupTy : ∀ {n} -> (H : Heap n) -> (fn : Fin n) -> Type
-- lookupTy (Cons {ty} v H) Data.Fin.zero = ty
-- lookupTy (Cons v H) (Data.Fin.suc f) = lookupTy H f


data Elem : ∀ {n} -> Heap n -> ℕ -> Type -> Set where
  Current : ∀ {n ty} {v : Value ty} {H : Heap n} -> Elem (Cons v H) n ty
  Skip    : ∀ {n ty i ty'} {v : Value ty'} {H : Heap n} -> (i Data.Nat.< n) -> (Elem {n} H i ty) -> Elem {suc n} (Cons v H) i ty


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


≤next : ∀ {n m} -> (n Data.Nat.≤ m) -> ((suc n) Data.Nat.≤ (suc m))
≤next z≤n = s≤s z≤n
≤next (s≤s le) = s≤s (≤next le)

≤plus : ∀ {n m} -> n Data.Nat.≤ (n + m)
≤plus {zero} {zero} = z≤n
≤plus {suc n} {m} = s≤s (≤plus {n} {m})
≤plus {zero} {suc m} = z≤n

≤elim : ∀ {n} -> (suc n) Data.Nat.≤ n -> ⊥
≤elim {zero} ()
≤elim {suc n} (s≤s ss) = ≤elim ss

elem-eq : ∀ {n ty ty₁} {H : Heap n} {v : Value ty} -> (e : Elem {suc n} (Cons v H) n ty₁) -> (ty₁ ≡ ty)
elem-eq Current = refl
elem-eq (Skip {i} {_} .{i} x e) = ⊥-elim (f x)
  where f : ∀ {i} -> (suc i) Data.Nat.≤ i -> ⊥
        f {zero} ()
        f {suc i₁} (s≤s s) = f s


elem? : ∀ {n} -> (H : Heap n) -> (fn : ℕ) -> (ty : Type) -> ((Elem {n} H fn ty) ⊎ (¬ (Elem {n} H fn ty)))
elem? Nil i ty = inj₂ g
  where g : ∀ {ty i} -> Elem Nil i ty -> ⊥
        g ()
elem? (Cons {ty} {n} v H) i ty₁ with compare i n
elem? (Cons v H) i ty₁ | less .i k with elem? H i ty₁
elem? (Cons v H) i ty₁ | less .i k | inj₁ x = inj₁ (Skip {suc (i + k)} {ty₁} {i} {_} {v} {H} (≤plus) x)
elem? (Cons v H) i ty₁ | less .i k | inj₂ y = inj₂ (λ x → y (g {_} {_} {_} {i} {v} {H} (≤plus) x))
  where g : ∀ {ty ty₁ n i} {v : Value ty₁} {H : Heap n} -> (i Data.Nat.< n) -> Elem (Cons v H) i ty -> Elem H i ty
        g lt Current = ⊥-elim (≤elim lt)
        g lt (Skip x e) = e
elem? (Cons {ty} {n} v H) .n ty₁ | equal .n with tyEq ty₁ ty
elem? (Cons {ty} {n} v H) .n .ty | equal .n | inj₁ refl = inj₁ Current
elem? (Cons {ty} {n} v H) .n ty₁ | equal .n | inj₂ y = inj₂ (λ x → y (elem-eq x))
elem? (Cons {ty} {n} v H) .(suc (n + k)) ty₁ | greater .n k = inj₂ (λ x → g ≤plus x)
  where h : ∀ {m n} -> (suc m) Data.Nat.≤ n -> (suc n) Data.Nat.≤ m -> ⊥
        h {zero} a ()
        h {suc m} {zero} () b
        h {suc m} {suc n₁} (s≤s a) (s≤s b) = h a b
        g : ∀ {ty ty1 n m} {v : Value ty1} {H : Heap n} -> (m Data.Nat.> n) -> (Elem (Cons v H) m ty) -> ⊥
        g leq Current = ≤elim leq
        g leq (Skip x e) = h leq x


replace : ∀ {ty n} -> {fn : ℕ} -> (H : Heap n) -> Elem H fn ty -> Value ty -> Heap n
replace .(Cons v H) (Current {i} {ty} {v} {H}) v₁ = Cons v₁ H
replace .(Cons v H) (Skip {n} {ty} {i} {ty'} {v} {H} x e) v₁ = Cons v (replace H e v₁)
