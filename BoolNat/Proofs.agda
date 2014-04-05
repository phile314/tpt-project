-- This module contains the metatheories proved for the language

module Proofs where

open import Base
open import SmallStep
open import BigStep
open import Denotational
open import Data.Unit using (unit)
open import Data.Sum
open import Data.Product using ( ∃ ; _,_)
open import Data.Nat 
open import Relation.Binary.PropositionalEquality



-- Proof that the heap only grows.
no-shrink :  ∀ {ty n m} {H1 : Heap n} {H2 : Heap m} {t1 t2 : Term ty} -> Step {H1 = H1} {H2 = H2} t1 t2 -> n ≤′ m
no-shrink (E-Succ stp) = no-shrink stp
no-shrink E-IsZeroZero = ≤′-refl
no-shrink (E-IsZeroSucc x) = ≤′-refl
no-shrink (E-IsZero stp) = no-shrink stp
no-shrink E-IfTrue = ≤′-refl
no-shrink E-IfFalse = ≤′-refl
no-shrink (E-If stp) = no-shrink stp
no-shrink (E-New stp) = no-shrink stp
no-shrink E-NewVal = ≤′-step ≤′-refl
no-shrink (E-Deref stp) = no-shrink stp
no-shrink E-DerefVal = ≤′-refl
no-shrink (E-AssLeft stp) = no-shrink stp
no-shrink (E-AssRight isV stp) = no-shrink stp
no-shrink E-AssRed = ≤′-refl
no-shrink (E-Try-Catch stp) = no-shrink stp
no-shrink (E-Try-Catch-Suc x) = ≤′-refl
no-shrink E-Try-Catch-Fail = ≤′-refl
no-shrink E-Succ-Err = ≤′-refl
no-shrink E-IsZero-Err = ≤′-refl
no-shrink E-If-Err = ≤′-refl
no-shrink E-Deref-Err = ≤′-refl
no-shrink E-Assign-Err1 = ≤′-refl

deterministic : ∀ {ty n m1 m2} {H : Heap n} {H1 : Heap m1} {H2 : Heap m2} {t t1 t2 : Term ty} ->
                Step {H1 = H} {H2 = H1} t t1 -> Step {H1 = H} {H2 = H2} t t2 -> t1 ≡ t2
deterministic s1 s2 = {!!}

-- Progress and preservation
progress : ∀ {ty n m} {H1 : Heap n} {H2 : Heap m} -> (t : Term ty) -> ((isValue t) ⊎ (∃ (Step {H1 = H1} {H2 = H2} t)))
progress true = inj₁ unit
progress false = inj₁ unit
progress error = inj₁ unit
progress zero = inj₁ unit
progress {.Natural} {_} {_} {H1} {H2} (succ t) with progress {_} {_} {_} {H1} {H2} t
progress (succ t) | inj₁ x = inj₁ x
progress (succ t) | inj₂ y = {!!}
progress (iszero t) = {!!}
progress (if t then t₁ else t₂) = {!!}
progress (new t) = {!!}
progress (! t) = {!!}
progress (t <- t₁) with progress t | progress t₁
progress (t <- t₁) | inj₁ x | inj₁ x₁ = inj₂ {!!}
progress (t <- t₁) | inj₁ x | inj₂ y = {!!}
progress (t <- t₁) | inj₂ y | inj₁ x = {!!}
progress (t <- t₁) | inj₂ y | inj₂ y₁ = {!!}
progress (ref x) = {!!}
progress (try t catch t₁) = {!!} 

preservation : ∀ {ty n m} {H1 : Heap n} {H2 : Heap m} {t : Term ty} {t' : Term ty} -> Step {H1 = H1} {H2 = H2} t t' -> ty ≡ ty
preservation stp = refl

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
termination H zero = Halts (vnat zero) H []
termination H (succ t) with termination H t
termination H (succ t) | Halts (vnat x) H2 x₁ = Halts (vnat (suc x)) H2 {!E-Succ*!} -- E-Succ applied enough times
termination H (succ t) | Halts verror H2 x = Halts verror H2 {!!}  -- Build explicitly list of steps using Succ-Err
termination H (iszero t) = {!!}
termination H (if t then t₁ else t₂) = {!!}
termination H (new t) = {!!}
termination H (! t) = {!!}
termination H (t <- t₁) = {!!}
termination H (ref x) = {!!}
termination H (try t catch t₁) = {!!}

--------------------------------------------------------------------------------
-- Big step is Complete and Sound
--------------------------------------------------------------------------------

-- Not completely sure if the definitions are correct and if they will work out

⇓complete : ∀ {ty n m} {H1 : Heap n} {H2 : Heap m} (t : Term ty) (v : Value ty) ->
            ⟦ t ⟧ H1 ≡ < v , H2 > -> BStep {H1 = H1} {H2 = H2} t v 
⇓complete = {!!}

⇓sound : ∀ {ty n m} {H1 : Heap n} {H2 : Heap m} (t : Term ty) (v : Value ty) -> 
         BStep {H1 = H1} {H2 = H2} t v -> ⟦ t ⟧ H1 ≡ < v , H2 >
⇓sound = {!!}
