module Denotational where

open import BoolNat
open import Data.Nat
open import Data.Unit

------------------------------------------------------------------------
-- Denotational semantics.

-- I don't think we need this anymore
-- Maps an already evaluated term in the value world (does not use ⟦ _ ⟧)
⌞_⌟ : ∀ {ty} -> (t : Term ty) -> isValue t -> Value ty
⌞_⌟ true v = vtrue
⌞_⌟ false v = vfalse
⌞_⌟ zero v = vnat zero
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
isValue? (vnat zero) = unit
isValue? (vnat (suc n)) = isValue? (vnat n) 
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
⟦ zero ⟧ H = (vnat zero , Same H)
⟦ succ t ⟧ H with ⟦ t ⟧ H 
⟦_⟧ (succ t) H | vnat n , δ = (vnat (suc n)) , δ 
⟦ iszero t ⟧ H with ⟦ t ⟧ H
⟦ iszero t ⟧ H | ( v , δ ) = (vtrue , δ) 
⟦_⟧ {Ref ty} (new t) H with ⟦ t ⟧ H
⟦_⟧ {Ref ty} (new t) H | _,_ {S2 = S2} v δ = vref (Top {S2}) , Allocate v δ
⟦_⟧ (! t) H with ⟦_⟧ t H
-- Here I would need to map the term back to the value, but I cannot use ⟦ ⟧ or it might not terminate
⟦_⟧ {S = S0} (! t) H | _,_ {S1 = S1} {S2 = S2} {s = s} {H2 = H2} (vref {S = S} x) δ = lookup H2 (weaken {!s!} x) , δ
⟦ t <- t₁ ⟧ H with ⟦ t ⟧ H
⟦_⟧ (t <- t₁) H | _,_ {H2 = H1} v δ1 with ⟦ t₁ ⟧ H1
⟦_⟧ (t <- t₁) H | vref x , δ2 | v , δ = v , Replace {!!} v δ2 -- replace ? {!!} ⌜ v ⌝ (isValue? v)
⟦ ref e ⟧ H = vref e , Same H

_~>_ {H2 = H2} δ t = ⟦ t ⟧ H2 
