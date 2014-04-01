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
-- Shape
--------------------------------------------------------------------------------

data Shape : Set where
  Nil : Shape
  Cons : Type -> Shape -> Shape

data Elem : Shape -> Type -> Set where
  Top : forall {S ty} -> Elem (Cons ty S) ty
  Pop : forall {S ty a} -> Elem S ty -> Elem (Cons a S) ty

-- View function
-- WARNING : Here we return the Elem proof object for the first element of the same type.
-- However an Elem object does not necessarely need to refer to the first occurence. 
-- This could lead to inconsistences in the proofs.
elem : (S : Shape) -> (ty : Type) -> Maybe (Elem S ty) 
elem Nil ty = nothing
elem (Cons ty' S) ty with ty' =? ty
elem (Cons .ty S) ty | just refl = just Top
elem (Cons ty' S) ty | nothing with elem S ty
elem (Cons ty' S) ty | nothing | just x = just (Pop x)
elem (Cons ty' S) ty | nothing | nothing = nothing

-- xs ⊆ ys i.e. ∃ zs : xs ≡  zs ++ ys
data _⊆_ : Shape -> Shape -> Set where
  Same : ∀ {s} -> s ⊆ s
  Grow : ∀ {s1 s2 ty} -> s1 ⊆ s2 -> s1 ⊆ (Cons ty s2)
 
-- If S' is a prefix of S an element of S' is also an element S
weaken : ∀ {ty S S'} -> S' ⊆ S -> Elem S' ty -> Elem S ty
weaken Same p = p
weaken (Grow isP) p = Pop (weaken isP p)

trans⊆ : ∀ {S1 S2 S3} -> S1 ⊆ S2 -> S2 ⊆ S3 -> S1 ⊆ S3
trans⊆ Same s2 = s2
trans⊆ (Grow s1) Same = Grow s1
trans⊆ (Grow s1) (Grow s2) = Grow (trans⊆ (Grow s1) s2)

--------------------------------------------------------------------------------
-- Terms and syntax and type rules.
--------------------------------------------------------------------------------

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
 _<-_          : forall {ty} -> Term (Ref ty) -> Term ty -> Term ty
 ref           : forall {S ty} -> Elem S ty -> Term (Ref ty)


--------------------------------------------------------------------------------
-- Values
--------------------------------------------------------------------------------

data Value : Type -> Set where
  vtrue vfalse : Value Boolean
  vnat : Nat -> Value Natural
  vref : ∀ {ty S} -> Elem S ty -> Value (Ref ty)

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
isValue (_<-_ t t₁) = ⊥

-- Maps a value back in the term world
⌜_⌝ : ∀ {ty} -> Value ty -> Term ty
⌜ vtrue ⌝ = true
⌜ vfalse ⌝ = false
⌜ vnat zero ⌝ = zero
⌜ vnat (suc n) ⌝ = succ ⌜ vnat n ⌝
⌜ vref x ⌝ = ref x

--------------------------------------------------------------------------------
-- Heap
--------------------------------------------------------------------------------

data Heap : Shape -> Set where
  Nil : Heap Nil
  Cons : forall {ty} -> (v : Value ty) -> (s : Shape) -> Heap s -> Heap (Cons ty s)

lookup : forall {ty S} -> Heap S -> Elem S ty -> Value ty
lookup (Cons v S xs) Top = v
lookup (Cons v S xs) (Pop p) = lookup xs p

--------------------------------------------------------------------------------
-- Delta
--------------------------------------------------------------------------------

mutual
  data Δ : ∀ {S1 S2} -> S1 ⊆ S2 -> Heap S1 -> Heap S2 -> Set where
    Same      : ∀ {S} -> (H : Heap S) -> Δ Same H H
    Allocate  : ∀ {ty S1 S2} {s : S1 ⊆ S2} {H1 : Heap S1} {H2 : Heap S2} (v : Value ty) ->
                   Δ s H1 H2 -> Δ (Grow s) H1 (Cons v S2 H2)
    Replace   : ∀ {ty S1 S2} {s : S1 ⊆ S2} {H1 : Heap S1} {H2 : Heap S2} (e : Elem S2 ty) (v : Value ty) ->
                   Δ s H1 H2 -> Δ s H1 (replace H2 e v)  

  replace : ∀ {ty S} -> Heap S -> Elem S ty -> (v : Value ty) -> Heap S
  replace (Cons v S xs) Top v' = Cons v' S xs
  replace (Cons v S xs) (Pop p) v' = Cons v S (replace xs p v')

trans⊆Grow : ∀ {ty S1 S2 S3} (s12 : S1 ⊆ S2) -> (s23 : S2 ⊆ S3) -> trans⊆ s12 (Grow {ty = ty} s23) ≡ Grow (trans⊆ s12 s23)
trans⊆Grow Same s23 = refl
trans⊆Grow (Grow s12) s23 = refl 

-- Concatenates deltas 
_<++>_ :  {S1 S2 S3 : Shape} {s12 : S1 ⊆ S2} {s23 : S2 ⊆ S3} {H1 : Heap S1} {H2 : Heap S2} {H3 : Heap S3} ->   
          Δ s12 H1 H2 -> Δ s23 H2 H3 -> Δ (trans⊆ s12 s23) H1 H3
_<++>_ {.S2} {S2} {S3} {.Same} {s2} {.H2} {H2} (Same .H2) δ2 = δ2
Allocate {ty} {._} {S2} {s} {._} {H2} v δ1 <++> Same .(Cons v S2 H2) = Allocate v δ1
Allocate v δ1 <++> Allocate v₁ δ2 = Allocate v₁ (Allocate v δ1 <++> δ2)
Allocate v δ1 <++> Replace e v₁ δ2 = Replace e v₁ (Allocate v δ1 <++> δ2)
Replace {ty} {._} {._} {._} {._} {H2} e v δ1 <++> Same .(replace H2 e v) = Replace e v (δ1 <++> Same H2)
_<++>_  {S3 = Cons ty S3} {s12 = s12} {s23 = Grow s23} (Replace e v δ1) (Allocate v₁ δ2) rewrite trans⊆Grow {ty} s12 s23 = Allocate v₁ (Replace e v δ1 <++> δ2)
Replace e v δ1 <++> Replace e₁ v₁ δ2 = Replace e₁ v₁ (Replace e v δ1 <++> δ2)
