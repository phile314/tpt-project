module Denotational where

open import Base
open import Data.Nat
open import Data.Unit
open import Data.Maybe
open import Data.Sum

------------------------------------------------------------------------
-- Denotational semantics.

-- The result of an evaluation. 
-- Since the evaluation affects the Heap (state), it needs to be returned as well.
record Result (ty : Type) : Set where
  constructor <_,_>
  field 
    { n } : ℕ
    value : Value ty
    heap  :  Heap n

-- Evaluation function.
-- The Heap is a chained attribute, it is threaded through all the recursicve call.
⟦_⟧ : ∀ {ty n} -> Term ty → Heap n -> Result ty
⟦_⟧ true H = < vtrue , H >
⟦_⟧ false H = < vfalse , H >
⟦_⟧ error H = < verror , H >
⟦_⟧ (num n) H = < (vnat n) , H >
⟦_⟧ (iszero t) H with ⟦ t ⟧ H
⟦_⟧ (iszero t) H | < vnat zero , H' > = < vtrue , H' >
⟦_⟧ (iszero t) H | < vnat (suc x) , H' > = < vfalse , H' >
⟦_⟧ (iszero t) H | < verror , H' > = < verror , H' >
⟦_⟧ (if t then t₁ else t₂) H with ⟦ t ⟧ H
⟦_⟧ (if t then t₁ else t₂) H | < vtrue , H' > = ⟦ t₁ ⟧ H'
⟦_⟧ (if t then t₁ else t₂) H | < vfalse , H' > = ⟦ t₂ ⟧ H'
⟦_⟧ (if t then t₁ else t₂) H | < verror , H' > = < verror , H' >
⟦_⟧ (new t) H with ⟦ t ⟧ H
-- We allow also error to be stored in the heap
⟦_⟧ (new t) H | <_,_> {n} v H' = < (vref n) , (append H' v) >  -- Consistent with the current small step (cons instead of append)
⟦_⟧ (! t) H with ⟦ t ⟧ H
⟦_⟧ (! t) H | < vref x , H' > = < (lookup x H') , H' >
⟦_⟧ (! t) H | < verror , H' > = < verror , H' >
⟦_⟧ (t <- t₁) H with ⟦ t ⟧ H
⟦_⟧ (t <- t₁) H | < vref n , H₁ > with ⟦ t₁ ⟧ H₁
⟦_⟧ {ty} (t <- t₁) H | < vref n , H₁ > | < v , H₂ > with elem? H₂ n ty
⟦_⟧ (t <- t₁) H | < vref n₁ , H₁ > | < v , H₂ > | inj₁ x = < v , replace H₂ x v >
⟦_⟧ (t <- t₁) H | < vref n₁ , H₁ > | < v , H₂ > | inj₂ y = < verror , H₂ >
⟦_⟧ (t <- t₁) H | < verror , H₁ > = < verror , H₁ >
⟦_⟧ (ref x) H = < vref x , H >
⟦_⟧ (try t catch t₁) H with ⟦ t ⟧ H
⟦_⟧ (try t catch t₁) H | < verror , H' > = ⟦ t₁ ⟧ H'
⟦_⟧ (try t catch t₁) H | < v , H' > = < v , H' >
⟦_⟧ (t >> t₁) H with ⟦ t ⟧ H
⟦_⟧ (t >> t₁) H | < verror , H' > = < verror , H' >
⟦_⟧ (t >> t₁) H | < v , H' > = ⟦ t₁ ⟧ H'
