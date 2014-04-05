module BigStep where

open import Data.Nat
open import Base
open import SmallStep

-- TODO: there should be no isValue proofs in the big steps. Instead take another bigstep as parameter which reduces the argment to a value. (e.g. E-New)

data BStep : ∀ {ty n m} {H1 : Heap n} {H2 : Heap m} -> Term ty → Value ty → Set where

  E-True    : ∀ {n} {H : Heap n} → BStep {H1 = H} {H2 = H} true vtrue

  E-False   : ∀ {n} {H : Heap n} → BStep {H1 = H} {H2 = H} false vfalse

  E-IfTrue  : ∀ {ty} {n1 n2 n3} {H1 : Heap n1} {H2 : Heap n2} {H3 : Heap n3} 
                 {t : Term Boolean} {t1 t2 : Term ty} {v : Value ty} →
              BStep {H1 = H1} {H2 = H2} t  vtrue → 
              BStep {H1 = H2} {H2 = H3} t1 v     →
              BStep {H1 = H1} {H2 = H3} (if t then t1 else t2) v

  E-IfFalse  : ∀ {ty} {n1 n2 n3} {H1 : Heap n1} {H2 : Heap n2} {H3 : Heap n3} 
                 {t : Term Boolean} {t1 t2 : Term ty} {v : Value ty} →
              BStep {H1 = H1} {H2 = H2} t  vfalse → 
              BStep {H1 = H2} {H2 = H3} t2 v     →
              BStep {H1 = H1} {H2 = H3} (if t then t1 else t2) v


--   E-Zero    : ∀ {S} {H : Heap S} →
--               BStep (Same H) zero (vnat 0)

--   E-Succ    : ∀ {S1 S2} {s : S1 ⊆ S2} {H1 : Heap S1} {H2 : Heap S2} {δ : Δ s H1 H2} {n : Term Natural} {vn : ℕ} → 
--               BStep δ n        (vnat vn) →
--               BStep δ (succ n) (vnat (1 + vn))

--   E-IsZeroZ : ∀ {S1 S2} {s : S1 ⊆ S2} {H1 : Heap S1} {H2 : Heap S2} {δ : Δ s H1 H2} {n : Term Natural} →

--               BStep δ n          (vnat 0) →
--               BStep δ (iszero n) vtrue

--   E-IsZeroS : ∀ {S1 S2} {s : S1 ⊆ S2} {H1 : Heap S1} {H2 : Heap S2} {δ : Δ s H1 H2} {n : Term Natural} {n' : ℕ} →
--               BStep δ n          (vnat (suc n')) →
--               BStep δ (iszero n) vfalse

--   E-New     : ∀ {ty S1 S2} {s : S1 ⊆ S2} {H1 : Heap S1} {H2 : Heap S2} {δ : Δ s H1 H2} {t : Term ty} {v : Value ty} →
--               BStep δ t v ->
--               BStep (Allocate v δ) (new t) (vref {!!})
--   E-Ref     : ∀ {S} {H : Heap S} →
--               BStep (Same H) (ref {!!}) (vref {!!})
--   E-Assign  : ∀ {ty S1 S2} {s : S1 ⊆ S2} {H1 : Heap S1} {H2 : Heap S2} {δ : Δ s H1 H2} {t : Term ty} {v : Value ty} ->
--               BStep δ t v → 
--               BStep (Replace {!!} v δ) (ref {!!} <- t) v
--   E-Deref   : ∀ {ty S} {H : Heap S} {v : Value ty} →
--               BStep (Same H) (! (ref {!!})) (lookup H {!!})

-- -- TODO here we need to add all the failing big steps
--   E-Err     : ∀ {ty S1 S2} {s : S1 ⊆ S2} {H1 : Heap S1} {H2 : Heap S2} {δ : Δ s H1 H2} -> BStep {ty} δ error verror


--------------------------------------------------------------------------------
-- Conversion between BigStep and SmallStep
--------------------------------------------------------------------------------

-- An extension of the E-If rule, for multiple steps.
E-If* : ∀ {ty n m} {H1 : Heap n} {H2 : Heap m} {t₁ t₁′ : Term Boolean} {t₂ t₃ : Term ty} →
        Steps {H1 = H1} {H2 = H2} t₁ t₁′ →
        Steps {H1 = H1} {H2 = H2} (if t₁ then t₂ else t₃) (if t₁′ then t₂ else t₃)
E-If* [] = []
E-If* (x :: stps) = E-If x :: E-If* stps


-- -- Lemmas used for small-to-big
-- -- Converstion from big- to small-step representations.
big-to-small : forall {ty n m} {H1 : Heap n} {H2 : Heap m} {t : Term ty} {v : Value ty} ->
               BStep {H1 = H1} {H2 = H2} t v -> Steps {H1 = H1} {H2 = H2} t ⌜ v ⌝
big-to-small E-True = []
big-to-small E-False = []
big-to-small (E-IfTrue bstp bstp₁) = E-If* (big-to-small bstp) ++ (E-IfTrue :: (big-to-small bstp₁))
big-to-small (E-IfFalse bstp bstp₁) = E-If* (big-to-small bstp) ++ (E-IfFalse :: big-to-small bstp₁)

-- -- A value term evaluates to itself.
-- value-of-value : forall {ty n m} {H1 : Heap n} {H2 : Heap m} -> (v : Value ty) -> BStep {H1 = H1} {H2 = H2} ⌜ v ⌝ v
-- value-of-value = {!!}

-- -- Combining a single small step with a big step.
-- prepend-step : forall {ty n1 n2 n3} {H1 : Heap n1} {H2 : Heap n2} {H3 : Heap n3} {t1 t2 : Term ty} {v : Value ty} -> 
--                Step {H1 = H1} {H2 = H2} t1 t2 -> BStep {H1 = H2} {H2 = H3} t2 v -> BStep {H1 = H1} {H2 = H3} t1 v
-- prepend-step stp bstp = {!!}

-- small-to-big : ∀ {ty n m} {H1 : Heap n} {H2 : Heap m} {t : Term ty} {v : Value ty} → 
--                  BStep {H1 = H1} {H2 = H2} t v → Steps {H1 = H1} {H2 = H2} t ⌜ v ⌝
-- small-to-big = {!!}
