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
open import Relation.Nullary
open import Data.Empty renaming (⊥-elim to contradiction)

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
no-shrink (E-Try-Catch-Fail isE) = ≤′-refl
no-shrink E-Succ-Err = ≤′-refl
no-shrink E-IsZero-Err = ≤′-refl
no-shrink E-If-Err = ≤′-refl
no-shrink E-Deref-Err = ≤′-refl
no-shrink E-Assign-Err1 = ≤′-refl

-- A term is considered a normal form whenever it is not reducible.
NF : {ty : Type} -> Term ty → Set
NF {ty} t = ∀ {n m} {H1 : Heap n} {H2 : Heap m} (t' : Term ty) -> ¬ (Step {H1 = H1} {H2 = H2} t t')

term2NF : ∀ {ty} -> (t : Term ty) -> isValue t -> NF t
term2NF true isV t' ()
term2NF false isV t' ()
term2NF error isV t' ()
term2NF zero isV t' ()
term2NF (succ t) isV (succ t') (E-Succ stp) = term2NF t isV t' stp
term2NF (succ .error) isV .error E-Succ-Err = {!!}  -- isV should be empty
term2NF (iszero t) () t' stp
term2NF (if t then t₁ else t₂) () t' stp
term2NF (new t) () t' stp
term2NF (! t) () t' stp
term2NF (t <- t₁) () t' stp
term2NF (ref x) isV t' ()
term2NF (try t catch t₁) () t' stp

value2NF : ∀ {ty} -> (v : Value ty) -> NF ⌜ v ⌝
value2NF vtrue t ()
value2NF vfalse t ()
value2NF (vnat x) t stp = {!!}  -- Here stp should be an absurd pattern
value2NF (vref x) t ()
value2NF verror t ()

isError2isValue : ∀ {ty} -> (t : Term ty) -> isError t -> isValue t
isError2isValue true ()
isError2isValue false ()
isError2isValue error isE = unit
isError2isValue zero ()
isError2isValue (succ t) ()
isError2isValue (iszero t) ()
isError2isValue (if t then t₁ else t₂) ()
isError2isValue (new t) ()
isError2isValue (! t) ()
isError2isValue (t <- t₁) ()
isError2isValue (ref x) ()
isError2isValue (try t catch t₁) ()

deterministic : ∀ {ty n m1 m2} {H : Heap n} {H1 : Heap m1} {H2 : Heap m2} {t t1 t2 : Term ty} ->
                Step {H1 = H} {H2 = H1} t t1 -> Step {H1 = H} {H2 = H2} t t2 -> t1 ≡ t2
deterministic (E-Succ s1) (E-Succ s2) rewrite deterministic s1 s2 = refl
deterministic (E-Succ ()) E-Succ-Err
deterministic E-IsZeroZero E-IsZeroZero = refl
deterministic E-IsZeroZero (E-IsZero ())
deterministic (E-IsZeroSucc x) (E-IsZeroSucc x₁) = refl
deterministic (E-IsZeroSucc x) (E-IsZero s2) = contradiction (term2NF _ x _ s2)
deterministic (E-IsZero ()) E-IsZeroZero
deterministic (E-IsZero s1) (E-IsZeroSucc x) = contradiction (term2NF _ x _ s1)
deterministic (E-IsZero s1) (E-IsZero s2) rewrite deterministic s1 s2 = refl
deterministic (E-IsZero ()) E-IsZero-Err
deterministic E-IfTrue E-IfTrue = refl
deterministic E-IfTrue (E-If ())
deterministic E-IfFalse E-IfFalse = refl
deterministic E-IfFalse (E-If ())
deterministic (E-If ()) E-IfTrue
deterministic (E-If ()) E-IfFalse
deterministic (E-If s1) (E-If s2) rewrite deterministic s1 s2 = refl
deterministic (E-If ()) E-If-Err
deterministic (E-New s1) (E-New s2) rewrite deterministic s1 s2 = refl
deterministic (E-New s1) E-NewVal = contradiction (value2NF _ _ s1)
deterministic E-NewVal s2 = {!!} -- Very Problematic
deterministic (E-Deref s1) (E-Deref s2) rewrite deterministic s1 s2 = refl
deterministic (E-Deref ()) E-DerefVal
deterministic (E-Deref ()) E-Deref-Err
deterministic E-DerefVal (E-Deref ())
deterministic E-DerefVal E-DerefVal = refl
deterministic (E-AssLeft s1) (E-AssLeft s2) rewrite deterministic s1 s2 = refl
deterministic (E-AssLeft s1) (E-AssRight (isV , notE) s2) = contradiction (term2NF _ isV _ s1)
deterministic (E-AssLeft ()) E-AssRed
deterministic (E-AssLeft ()) E-Assign-Err1
deterministic (E-AssRight (isV , notE) s1) (E-AssLeft s2) = contradiction (term2NF _ isV _ s2)
deterministic (E-AssRight isV s1) (E-AssRight isV₁ s2) rewrite deterministic s1 s2 = refl
deterministic (E-AssRight isV s1) (E-AssRed {v = v}) = contradiction (value2NF v _ s1) -- Probably we should define E-AssRed differently
deterministic (E-AssRight (isV , notE) s1) E-Assign-Err1 = contradiction (notE unit) 
deterministic E-AssRed s2 = {!!} -- Probably we should define E-AssRed differently
deterministic (E-Try-Catch s1) (E-Try-Catch s2) rewrite deterministic s1 s2 = refl
deterministic (E-Try-Catch s1) (E-Try-Catch-Suc (isV , proj₂)) = contradiction (term2NF _ isV _ s1)
deterministic (E-Try-Catch s1) (E-Try-Catch-Fail isE) = contradiction (term2NF _ (isError2isValue _ isE) _ s1)
deterministic (E-Try-Catch-Suc (isV , proj₂)) (E-Try-Catch s2) = contradiction (term2NF _ isV _ s2)
deterministic (E-Try-Catch-Suc x) (E-Try-Catch-Suc x₁) = refl
deterministic (E-Try-Catch-Suc (isV , notE)) (E-Try-Catch-Fail isE) = contradiction (notE isE)
deterministic (E-Try-Catch-Fail isE) (E-Try-Catch s2) = contradiction (term2NF _ (isError2isValue _ isE) _ s2)
deterministic (E-Try-Catch-Fail isE) (E-Try-Catch-Suc (isV , notE)) = contradiction (notE isE)
deterministic (E-Try-Catch-Fail isE) (E-Try-Catch-Fail isE₁) = refl
deterministic E-Succ-Err (E-Succ ())
deterministic E-Succ-Err E-Succ-Err = refl
deterministic E-IsZero-Err (E-IsZero ())
deterministic E-IsZero-Err E-IsZero-Err = refl
deterministic E-If-Err (E-If ())
deterministic E-If-Err E-If-Err = refl
deterministic E-Deref-Err (E-Deref ())
deterministic E-Deref-Err E-Deref-Err = refl
deterministic E-Assign-Err1 (E-AssLeft ())
deterministic E-Assign-Err1 (E-AssRight (isV , notE) stp) = contradiction (notE unit)
deterministic E-Assign-Err1 E-Assign-Err1 = refl

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
