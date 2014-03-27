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

-- Maps an already evaluated term in the value world (does not use ⟦ _ ⟧)
⌞_⌟ : ∀ {ty} -> (t : Term ty) -> isValue t -> Value ty
⌞_⌟ true v = vtrue
⌞_⌟ false v = vfalse
⌞_⌟ zero v = vzero
⌞_⌟ (succ t) v = ⌞ t ⌟ v
⌞_⌟ (iszero t) ()
⌞_⌟ (if t then t₁ else t₂) ()
⌞_⌟ (new t) ()
⌞_⌟ (! t) ()
⌞_⌟ (t <- t₁) ()
⌞_⌟ (ref x) v = vref x

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
  _,_ : ∀ {ty S1 S2} {s : S1 ⊆ S2} {H1 : Heap S1} {H2 : Heap S2} -> (v : Value ty) -> Δ s H1 H2 -> State ty

-- Feeds the resulting heap of the delta in the evaluation of the term 
_~>_ : ∀ {ty S1 S2} {H1 : Heap S1} {H2 : Heap S2} {s : S1 ⊆ S2} -> Δ s H1 H2 -> Term ty -> State ty

-- Evaluation function.
-- The Heap is a chained attribute, it is threaded through all the recursicve call.
⟦_⟧ : ∀ {ty S} -> Term ty → Heap S -> State ty
⟦ true ⟧ H = (vtrue , Same H)
⟦ false ⟧ H = (vfalse , Same H)
⟦ if c then t else e ⟧ H with ⟦ c ⟧ H
⟦_⟧ (if c then t else e) H | vtrue , δ  = δ ~> t
⟦_⟧ (if c then t else e) H | vfalse , δ = δ ~> e
⟦ zero ⟧ H = (vzero , Same H)
⟦ succ t ⟧ H with ⟦ t ⟧ H 
⟦_⟧ (succ t) H | v , δ = vsucc v , δ 
⟦ iszero t ⟧ H with ⟦ t ⟧ H
⟦ iszero t ⟧ H | (vzero , δ ) = (vtrue , δ) 
⟦ iszero t ⟧ H | (vsucc n , δ) = (vfalse , δ)
⟦_⟧ {Ref ty} (new t) H with ⟦ t ⟧ H
⟦_⟧ {Ref ty} (new t) H | _,_ {S2 = S2} v δ = vref (Top {S2}) , Allocate {ty} {v = ⌜ v ⌝} {isV = isValue? v} δ
⟦_⟧ (! t) H with ⟦_⟧ t H
-- Here I would need to map the term back to the value, but I cannot use ⟦ ⟧ or it might not terminate
⟦_⟧ {S = S0} (! t) H | _,_ {S1 = S1} {S2 = S2} {s = s} {H2 = H2} (vref {S = S} x) δ with lookup H2 (weaken {!s!} x) 
... | p = ⌞ p ⌟ {!!} , δ
⟦ t <- t₁ ⟧ H with ⟦ t ⟧ H
⟦_⟧ (t <- t₁) H | _,_ {H2 = H1} v δ1 with ⟦ t₁ ⟧ H1
⟦_⟧ (t <- t₁) H | vref x , δ2 | v , δ = v , Replace {!!} ⌜ v ⌝ δ2 -- replace ? {!!} ⌜ v ⌝ (isValue? v)
⟦ ref e ⟧ H = vref e , Same H

_~>_ {H2 = H2} δ t = ⟦ t ⟧ H2 
