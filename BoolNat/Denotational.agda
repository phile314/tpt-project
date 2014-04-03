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
⌞_⌟ error v = verror 

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
⟦_⟧ (if c then t else e) H | (vtrue , δ)  = δ ~> t
⟦_⟧ (if c then t else e) H | (vfalse , δ) = δ ~> e
⟦_⟧ (if c then t else e) H | verror , x = verror , x
⟦ zero ⟧ H = (vnat zero , Same H)
⟦ succ t ⟧ H with ⟦ t ⟧ H 
⟦_⟧ (succ t) H | (vnat n , δ) = (vnat (suc n) , δ )
⟦_⟧ (succ t) H | verror , x = verror , x 
⟦ iszero t ⟧ H with ⟦ t ⟧ H
⟦_⟧ (iszero t) H | (vnat zero , δ) = (vtrue , δ) 
⟦_⟧ (iszero t) H | (vnat (suc x) , δ) =  (vfalse , δ)  
⟦_⟧ (iszero t) H | verror , x = verror , x 
⟦_⟧ {Ref ty} (new t) H with ⟦ t ⟧ H
⟦_⟧ {Ref ty} (new t) H | (_,_ {S2 = S2} v δ) = (vref {!!} , Allocate v δ)  -- Again the length of the Heap
⟦_⟧ (! t) H with ⟦ t ⟧ H
⟦_⟧ (! t) H | _,_ {H2 = H2} (vref n) x = lookup H2 n , Same H2
⟦_⟧ (! t) H | verror , x = verror , x 
⟦ t <- t₁ ⟧ H = {!!} 
⟦ ref e ⟧ H = (vref e , Same H)
⟦ error ⟧ H = verror , Same H

_~>_ {H2 = H2} δ t = ⟦ t ⟧ H2 
