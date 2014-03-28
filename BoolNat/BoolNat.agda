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

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

data Type : Set where
 Boolean : Type
 Natural : Type
 Ref : (ty : Type) -> Type

--------------------------------------------------------------------------------
-- Shape
--------------------------------------------------------------------------------

data Shape : Set where
  Nil : Shape
  Cons : Type -> Shape -> Shape

data Elem : Shape -> Type -> Set where
  Top : forall {S ty} -> Elem (Cons ty S) ty
  Pop : forall {S ty a} -> Elem S ty -> Elem (Cons a S) ty

-- xs ⊆ ys i.e. ∃ zs : xs ≡  zs ++ ys
data _⊆_ : Shape -> Shape -> Set where
  Same : ∀ {s} -> s ⊆ s
  Grow : ∀ {s1 s2 ty} -> s1 ⊆ s2 -> s1 ⊆ (Cons ty s2)
 
-- If S' is a prefix of S an element of S' is also an element S
weaken : ∀ {ty S S'} -> S' ⊆ S -> Elem S' ty -> Elem S ty
weaken Same p = p
weaken (Grow isP) p = Pop (weaken isP p)

trans : ∀ {S1 S2 S3} -> S1 ⊆ S2 -> S2 ⊆ S3 -> S1 ⊆ S3
trans Same s2 = s2
trans (Grow s1) Same = Grow s1
trans (Grow s1) (Grow s2) = Grow (trans (Grow s1) s2)

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
    Same : ∀ {S} -> (H : Heap S) -> Δ Same H H
    Allocate : ∀ {ty S1 S2} {s : S1 ⊆ S2} {H1 : Heap S1} {H2 : Heap S2} (v : Value ty) ->
               Δ s H1 H2 -> Δ (Grow s) H1 (Cons v S2 H2)
    Replace : ∀ {ty S1 S2} {s : S1 ⊆ S2} {H1 : Heap S1} {H2 : Heap S2} (e : Elem S2 ty) (v : Value ty) ->
              Δ s H1 H2 -> Δ s H1 (replace H2 e v)  

  replace : ∀ {ty S} -> Heap S -> Elem S ty -> (v : Value ty) -> Heap S
  replace (Cons v S xs) Top v' = Cons v' S xs
  replace (Cons v S xs) (Pop p) v' = Cons v S (replace xs p v')

-- Allocate v δ1 <++> Same (Cons .v S2 H2)  = Allocate δ1
-- Allocate δ1 <++> Allocate δ2 = Allocate (Allocate δ1 <++> δ2)
-- Allocate δ1 <++> Replace e t δ2 = Replace e t (Allocate δ1 <++> δ2) 
-- Replace {ty} {._} {._} {._} {._} {H2} e t {isV} δ1 <++> Same .(replace H2 e t isV) = Replace e t (δ1 <++> Same H2)
-- Replace e t δ1 <++> (Allocate δ2) = {!!} -- FIX : This is just looping : Replace e t δ1 <++> Allocate δ2
-- Replace e t δ1 <++> Replace e₁ t₁ δ2 = Replace e₁ t₁ (Replace e t δ1 <++> δ2)
