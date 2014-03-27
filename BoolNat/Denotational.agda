module Denotational where

open import BoolNat
open import Data.Nat
open import Data.Unit

------------------------------------------------------------------------
-- Denotational semantics.

-- Maps a value back in the term world
⌜_⌝ : ∀ {ty} -> Value ty -> Term ty
⌜ vtrue ⌝ = true
⌜ vfalse ⌝ = false
⌜ vzero ⌝ = zero
⌜ vsucc v ⌝ = succ ⌜ v ⌝
⌜ vref x ⌝ = ref x

-- View function for isValue. 
isValue? : ∀ {ty} -> (v : Value ty) -> isValue ⌜ v ⌝
isValue? vtrue = unit
isValue? vfalse = unit
isValue? vzero = unit
isValue? (vsucc v) = isValue? v
isValue? (vref x) = unit

-- The result of an evaluation. 
-- Since the evaluation affects the Heap (state), it needs to be returned as well.
data State : Type -> Set where
  _,_ : ∀ {ty S} -> (v : Value ty) -> (H : Heap S) -> State ty

-- Use Δ instead of H, so I get for free the proof S1 ⊆ S2

-- Evaluation function.
-- The Heap is a chained attribute, it is threaded through all the recursicve call.
⟦_⟧ : ∀ {ty S} -> Term ty → Heap S -> State ty
⟦ true ⟧ H = (vtrue , H)
⟦ false ⟧ H = (vfalse , H)
⟦ if c then t else e ⟧ H with ⟦ c ⟧ H
⟦_⟧ (if c then t else e) H | vtrue , H₁ = ⟦ t ⟧ H₁
⟦_⟧ (if c then t else e) H | vfalse , H₁ = ⟦ e ⟧ H₁
⟦ zero ⟧ H = (vzero , H)
⟦ succ t ⟧ H with ⟦ t ⟧ H 
⟦_⟧ (succ t) H | v , H₁ = v , H₁ 
⟦ iszero t ⟧ H with ⟦ t ⟧ H
⟦ iszero t ⟧ H | (vzero , H' ) = (vtrue , H') 
⟦ iszero t ⟧ H | (vsucc n , H') = (vfalse , H')
⟦ new t ⟧ H with ⟦ t ⟧ H
⟦_⟧ (new t) H | _,_ {S = S} v H₁ = (vref (Top {S})) , Cons ⌜ v ⌝ S (isValue? v) H₁
⟦ ! t ⟧ H with ⟦ t ⟧ H
-- Here I would need to map the term back to the value, but I cannot use ⟦ ⟧ or it might not terminate
⟦_⟧ (! t) H | vref x , H₁ = {!!} , H₁
⟦ t <- t₁ ⟧ H with ⟦ t ⟧ H
⟦_⟧ (t <- t₁) H | v , H₁ with ⟦ t₁ ⟧ H₁
⟦_⟧ (t <- t₁) H | vref x , H₁ | v , H₂ = v , replace H₂ {!!} ⌜ v ⌝ (isValue? v)
⟦ ref e ⟧ H = vref e , H
