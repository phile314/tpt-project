module BigStep where

open import Data.Nat
open import Data.Product
open import Data.Unit
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

  E-New     : ∀ {ty n m} {H1 : Heap n} {H2 : Heap m} {t : Term ty} {v : Value ty} →
              BStep {H1 = H1} {H2 = H2} t v ->
              BStep {H1 = H1} {H2 = Cons v H2} (new t) (vref 0)

  E-Deref   : ∀ {ty n m} {H : Heap n} {v : Value ty} →
              BStep {ty} {H1 = H} {H2 = H} (! (ref m)) (lookup m H)

  E-Assign  : ∀ {ty n m} {H1 : Heap n} {H2 : Heap m} {t : Term ty} {v : Value ty} ->
              BStep {H1 = H1} {H2 = H2} t v → 
              BStep {H1 = H1} {H2 = proj₁ (try-replace {H = H2} v) } (ref m <- t) (proj₂ (try-replace {H = H2} v))

  E-Error : ∀ {ty n} {H : Heap n} -> BStep {ty} {H1 = H} {H2 = H} error verror

  E-Zero    : ∀ {n} {H : Heap n} -> BStep {H1 = H} {H2 = H} zero (vnat 0)

  E-Succ    : ∀ {n m} {H1 : Heap n} {H2 : Heap m} {n : Term Natural} {vn : ℕ} → 
              BStep {H1 = H1} {H2 = H2} n        (vnat vn) →
              BStep {H1 = H1} {H2 = H2} (succ n) (vnat (1 + vn))

  E-Ref     : ∀ {n m ty} {H : Heap n} -> BStep {Ref ty} {H1 = H} {H2 = H} (ref m) (vref m)
  
--   E-IsZeroZ : ∀ {S1 S2} {s : S1 ⊆ S2} {H1 : Heap S1} {H2 : Heap S2} {δ : Δ s H1 H2} {n : Term Natural} →

--               BStep δ n          (vnat 0) →
--               BStep δ (iszero n) vtrue

--   E-IsZeroS : ∀ {S1 S2} {s : S1 ⊆ S2} {H1 : Heap S1} {H2 : Heap S2} {δ : Δ s H1 H2} {n : Term Natural} {n' : ℕ} →
--               BStep δ n          (vnat (suc n')) →
--               BStep δ (iszero n) vfalse

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

E-New* : ∀ {ty n m} {H1 : Heap n} {H2 : Heap m} {t t′ : Term ty} ->
        Steps {H1 = H1} {H2 = H2} t t′ →
        Steps {H1 = H1} {H2 = H2} (new t) (new t′)
E-New* [] = []
E-New* (x :: stps) = E-New x :: E-New* stps

E-Assign* : ∀ {ty n m r} {H1 : Heap n} {H2 : Heap m} {t t' : Term ty} ->
            Steps {H1 = H1} {H2 = H2} t t' -> 
            Steps {H1 = H1} {H2 = H2} (ref r <- t) (ref r <- t') 
E-Assign* [] = []
E-Assign* (x :: stps) = E-AssRight unit x :: E-Assign* stps

E-Succ* : ∀ {t t' n m} {H1 : Heap n} {H2 : Heap m} ->
          Steps {H1 = H1} {H2 = H2} t t' ->
          Steps {H1 = H1} {H2 = H2} (succ t) (succ t')
E-Succ* [] = []
E-Succ* (x :: stps) = E-Succ x :: E-Succ* stps

-- -- Lemmas used for small-to-big
-- -- Converstion from big- to small-step representations.
big-to-small : forall {ty n m} {H1 : Heap n} {H2 : Heap m} {t : Term ty} {v : Value ty} ->
               BStep {H1 = H1} {H2 = H2} t v -> Steps {H1 = H1} {H2 = H2} t ⌜ v ⌝
big-to-small E-True = []
big-to-small E-False = []
big-to-small E-Error = []
big-to-small E-Zero = []
big-to-small E-Ref = []
big-to-small (E-Succ bstp) = E-Succ* (big-to-small bstp)
big-to-small (E-IfTrue bstp bstp₁) = E-If* (big-to-small bstp) ++ (E-IfTrue :: big-to-small bstp₁)
big-to-small (E-IfFalse bstp bstp₁) = E-If* (big-to-small bstp) ++ (E-IfFalse :: big-to-small bstp₁)
big-to-small {H1 = H1} {H2 = Cons _ H2} {v = vref 0} (E-New bstp) = E-New* {H1 = H1} {H2 = H2} (big-to-small bstp) ++ [ E-NewVal ]
big-to-small E-Deref = E-DerefVal :: []
big-to-small {H2 = ._} (E-Assign bstp) = (E-Assign* (big-to-small bstp)) ++ [ E-AssRed { H2 = {!!} } ] 

-- -- A value term evaluates to itself.
value-of-value : forall {ty n} {H : Heap n} -> (v : Value ty) -> BStep {H1 = H} {H2 = H} ⌜ v ⌝ v
value-of-value vtrue = E-True
value-of-value vfalse = E-False
value-of-value (vnat zero) = E-Zero
value-of-value (vnat (suc x)) = E-Succ (value-of-value (vnat x))
value-of-value (vref x) = E-Ref
value-of-value verror = E-Error

-- -- Combining a single small step with a big step.
prepend-step : forall {ty n1 n2 n3} {H1 : Heap n1} {H2 : Heap n2} {H3 : Heap n3} {t1 t2 : Term ty} {v : Value ty} -> 
               Step {H1 = H1} {H2 = H2} t1 t2 -> BStep {H1 = H2} {H2 = H3} t2 v -> BStep {H1 = H1} {H2 = H3} t1 v
prepend-step (E-Succ stp) (E-Succ bstp) = E-Succ (prepend-step stp bstp)
prepend-step E-IsZeroZero bstp = {!!}
prepend-step (E-IsZeroSucc x) bstp = {!!}
prepend-step (E-IsZero stp) bstp = {!!}
prepend-step E-IfTrue bstp = E-IfTrue E-True bstp
prepend-step E-IfFalse bstp = E-IfFalse E-False bstp
prepend-step (E-If stp) (E-IfTrue bstp bstp₁) = E-IfTrue (prepend-step stp bstp) bstp₁
prepend-step (E-If stp) (E-IfFalse bstp bstp₁) = E-IfFalse (prepend-step stp bstp) bstp₁
prepend-step (E-New stp) (E-New bstp) = E-New (prepend-step stp bstp)
prepend-step E-NewVal E-Ref = {!!}  --- ?
prepend-step (E-Deref stp) E-Deref = {!!}   --- ?
prepend-step E-DerefVal bstp = {!!}
prepend-step (E-AssLeft stp) bstp = {!!}
prepend-step (E-AssRight isV stp) bstp = {!!}
prepend-step E-AssRed bstp = {!!}
prepend-step (E-Try-Catch stp) bstp = {!!}
prepend-step (E-Try-Catch-Suc x) bstp = {!!}
prepend-step E-Try-Catch-Fail bstp = {!!}
prepend-step E-Succ-Err bstp = {!!}
prepend-step E-IsZero-Err bstp = {!!}
prepend-step E-If-Err bstp = {!!}
prepend-step E-Deref-Err bstp = {!!}
prepend-step E-Assign-Err1 bstp = {!!}

small-to-big : ∀ {ty n m} {H1 : Heap n} {H2 : Heap m} {t : Term ty} {v : Value ty} → 
                 Steps {H1 = H1} {H2 = H2} t ⌜ v ⌝ -> BStep {H1 = H1} {H2 = H2} t v
small-to-big [] = value-of-value _
small-to-big (stp :: stps) = prepend-step stp (small-to-big stps)
