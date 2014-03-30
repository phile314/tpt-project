module Steps where

open import BoolNat
open import SmallStep

--------------------------------------------------------------------------------
-- Sequences of small steps.
--------------------------------------------------------------------------------

-- A sequence of steps that can be applied in succession.
data Steps : forall {ty} -> {S1 S2 : Shape} -> {H1 : Heap S1} -> {H2 : Heap S2} -> {s : S1 ⊆ S2} -> Δ s H1 H2 -> Term ty -> Term ty -> Set where
  []  : ∀ {ty} {S : Shape} {H : Heap S} {t : Term ty} -> Steps (Same H) t t
  _::_ : ∀ {ty} {S1 S2 S3 : Shape} {s1 : S1 ⊆ S2} {s2 : S2 ⊆ S3} {H1 : Heap S1} {H2 : Heap S2} {H3 : Heap S3} 
           {δ1 : Δ s1 H1 H2} {δ2 : Δ s2 H2 H3} {t1 t2 t3 : Term ty} ->
           Step δ1 t1 t2 -> Steps δ2 t2 t3 -> Steps (δ1 <++> δ2) t1 t3

-- -- Single-step sequence.
-- [_] : forall {ty S1 S2 H1 H2} {t1 t2 : Term ty} -> Step {ty} {S1} {S2} {H1} {H2} t1 t2 -> Steps {ty} {S1} {S2} {H1} {H2} t1 t2
-- [_] x = x :: [] 
  
