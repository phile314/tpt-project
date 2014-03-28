module Steps where

open import BoolNat
open import SmallStep

--------------------------------------------------------------------------------
-- Sequences of small steps.
--------------------------------------------------------------------------------

-- Move to BoolNat when finished
-- Concatenates deltas 
_<++>_ :  {S1 S2 S3 : Shape} {s1 : S1 ⊆ S2} {s2 : S2 ⊆ S3} {H1 : Heap S1} {H2 : Heap S2} {H3 : Heap S3} ->   
          Δ s1 H1 H2 -> Δ s2 H2 H3 -> Δ (trans s1 s2) H1 H3
_<++>_ {.S2} {S2} {S3} {.Same} {s2} {.H2} {H2} (Same .H2) δ2 = δ2
Allocate {ty} {._} {S2} {s} {._} {H2} v δ1 <++> Same .(Cons v S2 H2) = Allocate v δ1
Allocate v δ1 <++> Allocate v₁ δ2 = Allocate v₁ (Allocate v δ1 <++> δ2)
Allocate v δ1 <++> Replace e v₁ δ2 = Replace e v₁ (Allocate v δ1 <++> δ2)
Replace {ty} {._} {._} {._} {._} {H2} e v δ1 <++> Same .(replace H2 e v) = Replace e v (δ1 <++> Same H2)
Replace e v δ1 <++> Allocate v₁ δ2 = ?
Replace e v δ1 <++> Replace e₁ v₁ δ2 = Replace e₁ v₁ (Replace e v δ1 <++> δ2)

-- A sequence of steps that can be applied in succession.
data Steps : forall {ty} -> {S1 S2 : Shape} -> {H1 : Heap S1} -> {H2 : Heap S2} -> {s : S1 ⊆ S2} -> Δ s H1 H2 -> Term ty -> Term ty -> Set where
  []  : ∀ {ty} {S : Shape} {H : Heap S} {t : Term ty} -> Steps (Same H) t t
  _::_ : ∀ {ty} {S1 S2 S3 : Shape} {s1 : S1 ⊆ S2} {s2 : S2 ⊆ S3} {H1 : Heap S1} {H2 : Heap S2} {H3 : Heap S3} 
           {δ1 : Δ s1 H1 H2} {δ2 : Δ s2 H2 H3} {t1 t2 t3 : Term ty} ->
           Step δ1 t1 t2 -> Steps δ2 t2 t3 -> Steps (δ1 <++> δ2) t1 t3

-- -- Single-step sequence.
-- [_] : forall {ty S1 S2 H1 H2} {t1 t2 : Term ty} -> Step {ty} {S1} {S2} {H1} {H2} t1 t2 -> Steps {ty} {S1} {S2} {H1} {H2} t1 t2
-- [_] x = x :: [] 
  
