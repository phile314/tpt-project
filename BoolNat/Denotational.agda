module Denotational where

open import Base
open import Data.Nat
open import Data.Unit
open import Data.Maybe

------------------------------------------------------------------------
-- Denotational semantics.


-- View function for isValue. 
isValue? : ∀ {ty} -> (v : Value ty) -> isValue ⌜ v ⌝
isValue? vtrue = unit
isValue? vfalse = unit
isValue? (vnat zero) = unit
isValue? (vnat (suc n)) = isValue? (vnat n) 
isValue? (vref x) = unit
isValue? verror = unit

-- The result of an evaluation. 
-- Since the evaluation affects the Heap (state), it needs to be returned as well.
data Result : Type -> Set where
  <_,_> : ∀ {n ty} -> Value ty -> Heap n -> Result ty

-- Evaluation function.
-- The Heap is a chained attribute, it is threaded through all the recursicve call.
⟦_⟧ : ∀ {ty n} -> Term ty → Heap n -> Result ty
⟦_⟧ true H = < vtrue , H >
⟦_⟧ false H = < vfalse , H >
⟦_⟧ error H = < verror , H >
⟦_⟧ zero H = < (vnat 0) , H >
⟦_⟧ (succ t) H with ⟦ t ⟧ H
⟦_⟧ (succ t) H | < vnat x , H' > = < vnat (suc x) , H' >
⟦_⟧ (succ t) H | < verror , H' > = < verror , H' > 
⟦_⟧ (iszero t) H with ⟦ t ⟧ H
⟦_⟧ (iszero t) H | < vnat zero , H' > = < vtrue , H' >
⟦_⟧ (iszero t) H | < vnat (suc x) , H' > = < vfalse , H' >
⟦_⟧ (iszero t) H | < verror , H' > = < verror , H' >
⟦_⟧ (if t then t₁ else t₂) H with ⟦ t ⟧ H
⟦_⟧ (if t then t₁ else t₂) H | < vtrue , H' > = ⟦ t₁ ⟧ H'
⟦_⟧ (if t then t₁ else t₂) H | < vfalse , H' > = ⟦ t₂ ⟧ H'
⟦_⟧ (if t then t₁ else t₂) H | < verror , H' > = < verror , H' >
⟦_⟧ (new t) H with ⟦ t ⟧ H
⟦_⟧ (new t) H | < verror , H' > = < verror , H' >
⟦_⟧ (new t) H | < v , H' > = < (vref 0) , (Cons v H') >  -- Consistent with the current small step (cons instead of append)
⟦_⟧ (! t) H with ⟦ t ⟧ H
⟦_⟧ (! t) H | < vref x , H' > = < (lookup x H') , H' >
⟦_⟧ (! t) H | < verror , H' > = < verror , H' >
⟦_⟧ (t <- t₁) H with ⟦ t ⟧ H
⟦_⟧ (t <- t₁) H | < vref n , H₁ > with ⟦ t₁ ⟧ H₁
⟦_⟧ (t <- t₁) H | < vref n , H₁ > | < verror , H₂ > = < verror , H₂ >
⟦_⟧ {ty} (t <- t₁) H | < vref n , H₁ > | < v , H₂ > with replace? H₂ n ty
⟦_⟧ (t <- t₁) H | < vref n , H₁ > | < v , H₂ > | just x = < v , H₂ >
⟦_⟧ (t <- t₁) H | < vref n , H₁ > | < v , H₂ > | nothing = < verror , H₂ >
⟦_⟧ (t <- t₁) H | < verror , H₁ > = < verror , H₁ >
⟦_⟧ (ref x) H = < vref x , H >
⟦_⟧ (try t catch t₁) H with ⟦ t ⟧ H
⟦_⟧ (try t catch t₁) H | < verror , H' > = ⟦ t₁ ⟧ H'
⟦_⟧ (try t catch t₁) H | < v , H' > = < v , H' >
