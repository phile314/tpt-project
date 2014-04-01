module Denotational where

open import BoolNat
open import Data.Nat
open import Data.Unit
open import Data.Maybe

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
_~>_ : ∀ {ty S1 S2} {H1 : Heap S1} {H2 : Heap S2} {s : S1 ⊆ S2} -> Δ s H1 H2 -> Term ty -> Maybe (State ty)

-- Evaluation function.
-- The Heap is a chained attribute, it is threaded through all the recursicve call.
⟦_⟧ : ∀ {ty S} -> Term ty → Heap S -> Maybe (State ty)
⟦ true ⟧ H = just (vtrue , Same H)
⟦ false ⟧ H = just (vfalse , Same H)
⟦ if c then t else e ⟧ H with ⟦ c ⟧ H
⟦_⟧ (if c then t else e) H | just (vtrue , δ)  = δ ~> t
⟦_⟧ (if c then t else e) H | just (vfalse , δ) = δ ~> e
⟦_⟧ (if c then t else e) H | nothing = nothing
⟦ zero ⟧ H = just (vnat zero , Same H)
⟦ succ t ⟧ H with ⟦ t ⟧ H 
⟦_⟧ (succ t) H | just (vnat n , δ) = just (vnat (suc n) , δ )
⟦_⟧ (succ t) H | nothing = nothing 
⟦ iszero t ⟧ H with ⟦ t ⟧ H
⟦_⟧ (iszero t) H | just (vnat zero , δ) = just (vtrue , δ) 
⟦_⟧ (iszero t) H | just (vnat (suc x) , δ) = just (vfalse , δ)  
⟦ iszero t ⟧ H | nothing = nothing 
⟦_⟧ {Ref ty} (new t) H with ⟦ t ⟧ H
⟦_⟧ {Ref ty} (new t) H | just (_,_ {S2 = S2} v δ) = just (vref (Top {S2}) , Allocate v δ)
⟦_⟧ {Ref ty} (new t) H | nothing = nothing
⟦_⟧ (! t) H with ⟦_⟧ t H
⟦_⟧ {ty = ty} (! t) H | just (_,_  {S2 = S2} {H2 = H2} (vref x) δ) with elem S2 ty
... | just e = just ((lookup H2 e) , δ)
... | nothing = nothing
⟦_⟧ (! t) H | nothing = nothing
⟦ t <- t₁ ⟧ H with ⟦ t ⟧ H
⟦_⟧ (t <- t₁) H | nothing = nothing
⟦_⟧ (t <- t₁) H | just (_,_ {H2 = H1} v δ1) with ⟦ t₁ ⟧ H1
⟦_⟧ (t <- t₁) H | just (vref x , δ1) | just (_,_ {ty = ty} {S2 = S2} v  δ) with elem S2 ty
⟦_⟧ (t <- t₁) H | just (vref x₁ , δ1) | just (v , δ) | just e = just (v , Replace e v δ)
⟦_⟧ (t <- t₁) H | just (vref x , δ1) | just (v , δ) | nothing = nothing
⟦_⟧ (t <- t₁) H | just (vref x , δ2) | nothing = nothing
⟦ ref e ⟧ H = just (vref e , Same H)

_~>_ {H2 = H2} δ t = ⟦ t ⟧ H2 
