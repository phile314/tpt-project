module BigStep where

open import Data.Nat
open import BoolNat

data BStep : ∀ {ty S1 S2} {H1 : Heap S1} {H2 : Heap S2} {s : S1 ⊆ S2} -> Δ s H1 H2 → Term ty → Value ty → Set where
  E-True    : ∀ {S} {H : Heap S} → 
              BStep (Same H) true vtrue

  E-False   : ∀ {S} {H : Heap S} →
              BStep (Same H) false vfalse

  E-Zero    : ∀ {S} {H : Heap S} →
              BStep (Same H) zero (vnat 0)

  E-Succ    : ∀ {S1 S2} {s : S1 ⊆ S2} {H1 : Heap S1} {H2 : Heap S2} {δ : Δ s H1 H2} {n : Term Natural} {vn : ℕ} → 
              BStep δ n        (vnat vn) →
              BStep δ (succ n) (vnat (1 + vn))

  E-IsZeroZ : ∀ {S1 S2} {s : S1 ⊆ S2} {H1 : Heap S1} {H2 : Heap S2} {δ : Δ s H1 H2} {n : Term Natural} →
              BStep δ n          (vnat 0) →
              BStep δ (iszero n) vtrue

  E-IsZeroS : ∀ {S1 S2} {s : S1 ⊆ S2} {H1 : Heap S1} {H2 : Heap S2} {δ : Δ s H1 H2} {n : Term Natural} {n' : ℕ} →
              BStep δ n          (vnat (suc n')) →
              BStep δ (iszero n) vfalse

  E-IfTrue  : ∀ {ty} {S1 S2 S3} {s12 : S1 ⊆ S2} {s23 : S2 ⊆ S3} {H1 : Heap S1} {H2 : Heap S2} {H3 : Heap S3} {δ12 : Δ s12 H1 H2} {δ23 : Δ s23 H2 H3} {t : Term Boolean} {t1 t2 : Term ty} {v : Value ty} →
              BStep δ12 t  vtrue → 
              BStep δ23 t1 v     →
              BStep ({!!} δ12 δ23) (if t then t1 else t2) v -- Use <++> when finished

  E-IfFalse : ∀ {ty} {S1 S2 S3} {s12 : S1 ⊆ S2} {s23 : S2 ⊆ S3} {H1 : Heap S1} {H2 : Heap S2} {H3 : Heap S3} {δ12 : Δ s12 H1 H2} {δ23 : Δ s23 H2 H3} {t : Term Boolean} {t1 t2 : Term ty} {v : Value ty} →
              BStep δ12 t  vfalse →
              BStep δ23 t2 v      →
              BStep ({!!} δ12 δ23) (if t then t1 else t2) v -- Use <++> when finished

  E-New     : ∀ {ty S1 S2} {s : S1 ⊆ S2} {H1 : Heap S1} {H2 : Heap S2} {δ : Δ s H1 H2} {t : Term ty} {v : Value ty}{e : Elem S1 ty} →
              BStep δ t v ->
              BStep (Allocate v δ) (new t) (vref e)
  E-Ref     : ∀ {ty S} {H : Heap S} → {e : Elem S ty} →
              BStep (Same H) (ref e) (vref e)
  E-Assign  : ∀ {ty S1 S2} {s : S1 ⊆ S2} {H1 : Heap S1} {H2 : Heap S2} {δ : Δ s H1 H2} {t : Term ty} {v : Value ty} {e : Elem S2 ty} ->
              BStep δ t v → BStep (Replace e v δ) (ref e <- t) v
  E-Deref   : ∀ {ty S} {H : Heap S} {e : Elem S ty} {v : Value ty} →
              BStep (Same H) (! (ref e)) (lookup H e)

