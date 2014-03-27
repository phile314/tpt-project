module Steps where

open import BoolNat
open import SmallStep


-- Sequences of small steps.

trans : ∀ {S1 S2 S3} -> S1 ⊆ S2 -> S2 ⊆ S3 -> S1 ⊆ S3
trans Same s2 = s2
trans (Grow s1) Same = Grow s1
trans (Grow s1) (Grow s2) = Grow (trans (Grow s1) s2)

-- Concatenates deltas
_<++>_ :  {S1 S2 S3 : Shape} {s1 : S1 ⊆ S2} {s2 : S2 ⊆ S3} {H1 : Heap S1} {H2 : Heap S2} {H3 : Heap S3} ->   
          Δ s1 H1 H2 -> Δ s2 H2 H3 -> Δ (trans s1 s2) H1 H3
(Same H2) <++> δ2 = δ2
Allocate {ty} {._} {S2} {s} {._} {H2} {v} {isV} δ1 <++> Same .(Cons v S2 isV H2) = Allocate δ1
Allocate δ1 <++> Allocate δ2 = Allocate (Allocate δ1 <++> δ2)
Allocate δ1 <++> Replace e t δ2 = Replace e t (Allocate δ1 <++> δ2) 
Replace {ty} {._} {._} {._} {._} {H2} e t {isV} δ1 <++> Same .(replace H2 e t isV) = Replace e t (δ1 <++> Same H2)
Replace e t δ1 <++> (Allocate δ2) = {!!} -- FIX : This is just looping : Replace e t δ1 <++> Allocate δ2
Replace e t δ1 <++> Replace e₁ t₁ δ2 = Replace e₁ t₁ (Replace e t δ1 <++> δ2)

-- A sequence of steps that can be applied in succession.
data Steps : forall {ty} -> {S1 S2 : Shape} -> {H1 : Heap S1} -> {H2 : Heap S2} -> {s : S1 ⊆ S2} -> Δ s H1 H2 -> Term ty -> Term ty -> Set where
  []  : ∀ {ty} {S : Shape} {H : Heap S} {t : Term ty} -> Steps (Same H) t t
  _::_ : ∀ {ty} {S1 S2 S3 : Shape} {s1 : S1 ⊆ S2} {s2 : S2 ⊆ S3} {H1 : Heap S1} {H2 : Heap S2} {H3 : Heap S3} 
           {δ1 : Δ s1 H1 H2} {δ2 : Δ s2 H2 H3} {t1 t2 t3 : Term ty} ->
           Step δ1 t1 t2 -> Steps δ2 t2 t3 -> Steps (δ1 <++> δ2) t1 t3

-- -- Single-step sequence.
-- [_] : forall {ty S1 S2 H1 H2} {t1 t2 : Term ty} -> Step {ty} {S1} {S2} {H1} {H2} t1 t2 -> Steps {ty} {S1} {S2} {H1} {H2} t1 t2
-- [_] x = x :: [] 
  
