-- This module contains the metatheories proved for the language

module Proofs where

open import Base
open import SmallStep
open import BigStep
open import Denotational
open import Data.Sum
open import Data.Product using ( ∃ )
open import Data.Nat 
open import Relation.Binary.PropositionalEquality

-- Proof that the heap only grows.
no-shrink :  ∀ {ty n m} {H1 : Heap n} {H2 : Heap m} {t1 t2 : Term ty} -> Step {H1 = H1} {H2 = H2} t1 t2 -> n ≤ m
no-shrink stp = {!!}

deterministic : ∀ {ty n m1 m2} {H : Heap n} {H1 : Heap m1} {H2 : Heap m2} {t t1 t2 : Term ty} ->
                Step {H1 = H} {H2 = H1} t t1 -> Step {H1 = H} {H2 = H2} t t2 -> t1 ≡ t2
deterministic = {!!}

-- Progress and preservation
progress : ∀ {ty n m} {H1 : Heap n} {H2 : Heap m} -> (t : Term ty) -> ((isValue t) ⊎ (∃ (Step {H1 = H1} {H2 = H2} t)))
progress t = {!!} 

preservation : ∀ {ty n m} {H1 : Heap n} {H2 : Heap m} {t : Term ty} {t' : Term ty} -> Step {H1 = H1} {H2 = H2} t t' -> ty ≡ ty
preservation stp = refl

--------------------------------------------------------------------------------
-- Termination
--------------------------------------------------------------------------------

-- Still need to find a convinient way to express the Termination data type.


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
