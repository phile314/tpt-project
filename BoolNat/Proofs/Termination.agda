-- This module contains the metatheories proved for the language

module Proofs.Termination where

open import Base
open import SmallStep
open import BigStep
open import Denotational
open import Data.Unit using (unit)
open import Data.Sum
open import Data.Product using ( ∃ ; _,_)
open import Data.Nat 
open import Relation.Binary.PropositionalEquality hiding ( [_] )
open import Relation.Nullary
open import Data.Empty

--------------------------------------------------------------------------------
-- Termination
--------------------------------------------------------------------------------

-- With this formulation we cannot write the lemma prepend-steps.
-- I don't know whether inlining it would work.
-- I don't know if using another specific constructor would be better

data ⊢_↓_ {n : ℕ} {ty : Type} (H : Heap n) (t : Term ty) : Set where
  Halts : ∀ {m} (v : Value ty) -> (H2 : Heap m) -> Steps {H1 = H} {H2 = H2} t ⌜ v ⌝ -> ⊢ H ↓ t

prepend-steps : ∀ {ty n m} {H1 : Heap n} {H2 : Heap m} {t1 t2 : Term ty} -> Steps {H1 = H1} {H2 = H2} t1 t2  -> ⊢ H2 ↓ t2 -> ⊢ H1 ↓ t1
prepend-steps xs (Halts v H2 ys) = Halts v H2 (xs ++ ys)

termination : ∀ {ty n} -> (H : Heap n) -> (t : Term ty) -> ⊢ H ↓ t  
termination H true = Halts vtrue H []
termination H false = Halts vfalse H []
termination H error = Halts verror H []
termination H (num n) = Halts (vnat n) H []
termination H (iszero t) with termination H t
termination H (iszero t) | Halts (vnat zero) H2 xs = Halts vtrue H2 ((E-IsZero* xs) ++ [ E-IsZeroZero ])
termination H (iszero t) | Halts (vnat (suc x)) H2 xs = Halts vfalse H2 ((E-IsZero* xs) ++ [ E-IsZeroSucc ])
termination H (iszero t) | Halts verror H2 xs = Halts verror H2 ((E-IsZero* xs) ++ [ E-IsZero-Err ])
termination H (if t then t₁ else t₂) with termination H t
termination H (if t then t₁ else t₂) | Halts vtrue H2 xs = prepend-steps (E-If* xs ++ [ E-IfTrue ]) (termination H2 t₁)
termination H (if t then t₁ else t₂) | Halts vfalse H2 xs = prepend-steps ((E-If* xs) ++ [ E-IfFalse ]) (termination H2 t₂)
termination H (if t then t₁ else t₂) | Halts verror H2 xs = Halts verror H2 ((E-If* xs) ++ [ E-If-Err ])
termination H (new t) with termination H t
termination H (new t) | Halts v H2 xs = Halts (vref _) (Cons v H2) ((E-New* xs) ++ [ E-NewVal refl ])
termination H (! t) with termination H t
termination H (! t) | Halts (vref x) H2 xs = Halts (lookup x H2) H2 ((E-Deref* xs) ++ [ E-DerefVal ])
termination H (! t) | Halts verror H2 xs = Halts verror H2 ((E-Deref* xs) ++ [ E-Deref-Err ])
termination H (t <- t₁) with termination H t
termination H (t <- t₁) | Halts (vref x) H2 xs with termination H2 t₁
termination {ty} {n} H (t <- t₁) | Halts (vref x₁) H2 xs | Halts v H3 x with elem? H3 x₁ ty
termination H (t <- t₁) | Halts (vref x₁) H2 xs | Halts v H3 x₂ | inj₁ x = Halts v (replace H3 x v) ((E-AssignL* xs) ++ ((E-Assign* x₂) ++ [ (E-AssRed-Suc {_} {_} {_} {_} {H3} {_} {_} {isValue? v} refl x) ]))
termination {ty} H (t <- t₁) | Halts (vref x₁) H2 xs | Halts v H3 x | inj₂ y = Halts verror H3 ((E-AssignL* xs) ++ ((E-Assign* x) ++ [ (E-AssRed-Fail {ty} {_} {x₁} {_} {isValue? v} {H3} y) ]))
termination H (t <- t₁) | Halts verror H2 xs = Halts verror H2 (E-AssignL* xs ++ [ E-Assign-Err1 ])
termination H (ref x) = Halts (vref x) H []
termination H (try t catch t₁) with termination H t
termination H (try t catch t₁) | Halts verror H2 xs = prepend-steps (E-Try* xs ++ [ (E-Try-Catch-Fail unit) ]) (termination H2 t₁)
termination H (try t catch t₁) | Halts vtrue H2 xs = Halts vtrue H2 ((E-Try* xs) ++ [ E-Try-Catch-Suc (unit , (λ x → x)) ])
termination H (try t catch t₁) | Halts vfalse H2 xs = Halts vfalse H2 (E-Try* xs ++ [ E-Try-Catch-Suc (unit , (λ x → x)) ])
termination H (try t catch t₁) | Halts (vnat x) H2 xs = Halts (vnat x) H2 (E-Try* xs ++ [ E-Try-Catch-Suc (unit , (λ x → x)) ])
termination H (try t catch t₁) | Halts (vref x) H2 xs = Halts (vref x) H2 (E-Try* xs ++ [ E-Try-Catch-Suc (unit , (λ x → x)) ])
