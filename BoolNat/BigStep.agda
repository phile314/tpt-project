module BigStep where

open import Data.Nat
open import Data.Product
open import Data.Unit
open import Data.Sum
open import Data.Empty
open import Relation.Nullary
open import Base
open import SmallStep

open import Relation.Binary.PropositionalEquality hiding ( [_] ) -- remove

try-replace : ∀ {ty n} {H : Heap n} -> ℕ -> Value ty -> ((Heap n) × (Value ty))
try-replace {ty} {n} {H} i v with elem? H i ty
try-replace {_} {_} {H} i v | inj₁ x = replace H x v , v
try-replace {_} {_} {H} i v | inj₂ y = H , verror

replace-result : ∀ {n H fn ty} -> Value ty -> ((Elem {n} H fn ty) ⊎ (¬ (Elem {n} H fn ty))) -> Value ty
replace-result v (inj₁ x) = v
replace-result v (inj₂ y) = verror

replace-heap : ∀ {n H fn ty} -> Value ty -> ((Elem {n} H fn ty) ⊎ (¬ (Elem {n} H fn ty))) -> Heap n
replace-heap {_} {H} v (inj₁ x) = replace H x v
replace-heap {_} {H} v (inj₂ y) = H


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

  E-IfErr    : ∀ {ty} {n1 n2} {H1 : Heap n1} {H2 : Heap n2}
                 {t : Term Boolean} {t1 t2 : Term ty} →
              BStep {H1 = H1} {H2 = H2} t  verror → 
              BStep {H1 = H1} {H2 = H2} (if t then t1 else t2) verror

  E-New     : ∀ {ty n m} {H1 : Heap n} {H2 : Heap m} {t : Term ty} {v : Value ty} →
              BStep {H1 = H1} {H2 = H2} t v ->
              BStep {H1 = H1} {H2 = Cons v H2} (new t) (vref 0)

  E-Deref   : ∀ {ty n m r} {H1 : Heap n} {H2 : Heap m} {t : Term (Ref ty)} ->
              BStep {H1 = H1} {H2 = H2} t (vref r) ->
              BStep {H1 = H1} {H2 = H2} (! t) (lookup r H2)

  E-DerefErr : ∀ {ty n m} {H1 : Heap n} {H2 : Heap m} {t : Term (Ref ty)} ->
              BStep {H1 = H1} {H2 = H2} t verror ->
              BStep {H1 = H1} {H2 = H2} (! t) verror

  E-Assign  : ∀ {ty n m} {H1 : Heap n} {H2 : Heap m} {t : Term ty} {v : Value ty} ->
              BStep {H1 = H1} {H2 = H2} t v → 
              let e = elem? H2 m ty in
              BStep {ty} {n} {m} {H1 = H1} {H2 = replace-heap v e } (ref m <- t) (replace-result v e)

  E-Error : ∀ {ty n} {H : Heap n} -> BStep {ty} {H1 = H} {H2 = H} error verror

  E-Num    : ∀ {n m} {H : Heap n} -> BStep {H1 = H} {H2 = H} (num m) (vnat m)

  E-Ref     : ∀ {n m ty} {H : Heap n} -> BStep {Ref ty} {H1 = H} {H2 = H} (ref m) (vref m)
  
  E-IsZeroZ : ∀ {n1 n2} {H1 : Heap n1} {H2 : Heap n2} {t : Term Natural} →
              BStep {H1 = H1} {H2 = H2} t          (vnat 0) →
              BStep {H1 = H1} {H2 = H2} (iszero t) vtrue

  E-IsZeroS : ∀ {n1 n2} {H1 : Heap n1} {H2 : Heap n2} {t : Term Natural} {n : ℕ} →
              BStep {H1 = H1} {H2 = H2} t          (vnat (suc n)) →
              BStep {H1 = H1} {H2 = H2} (iszero t) vfalse

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
E-Assign* (x :: stps) = E-AssRight (unit , (λ x₁ → x₁)) x :: E-Assign* stps

E-AssignL* : ∀ {ty n m} {H1 : Heap n} {H2 : Heap m} {t t' : Term (Ref ty)} {t2 : Term ty} ->
            Steps {H1 = H1} {H2 = H2} t t' -> 
            Steps {H1 = H1} {H2 = H2} (t <- t2) (t' <- t2) 
E-AssignL* [] = []
E-AssignL* (x :: xs) = E-AssLeft x :: E-AssignL* xs

E-IsZero* : ∀ {t t' n m} {H1 : Heap n} {H2 : Heap m} ->
            Steps {H1 = H1} {H2 = H2} t t' ->
            Steps {H1 = H1} {H2 = H2} (iszero t) (iszero t')
E-IsZero* [] = []
E-IsZero* (x :: stps) = E-IsZero x :: E-IsZero* stps

E-Try* : ∀ {ty n m} {H1 : Heap n} {H2 : Heap m} {t t' t2 : Term ty} ->
            Steps {H1 = H1} {H2 = H2} t t' ->
            Steps {H1 = H1} {H2 = H2} (try t catch t2 ) (try t' catch t2)
E-Try* [] = []
E-Try* (x :: stps) = E-Try-Catch x :: E-Try* stps

E-Deref* : ∀ {ty n m} {H1 : Heap n} {H2 : Heap m} {t t' : Term (Ref ty)} ->
            Steps {H1 = H1} {H2 = H2} t t' ->
            Steps {H1 = H1} {H2 = H2} (! t) (! t')
E-Deref* [] = []
E-Deref* (x :: stps) = E-Deref x :: E-Deref* stps

-- Lemmas used for small-to-big
-- Converstion from big- to small-step representations.
-- big-to-small : forall {ty n m} {H1 : Heap n} {H2 : Heap m} {t : Term ty} {v : Value ty} ->
--                BStep {H1 = H1} {H2 = H2} t v -> Steps {H1 = H1} {H2 = H2} t ⌜ v ⌝
-- big-to-small E-True = []
-- big-to-small E-False = []
-- big-to-small E-Error = []
-- big-to-small E-Num = []
-- big-to-small E-Ref = []
-- big-to-small (E-IfTrue bstp bstp₁) = E-If* (big-to-small bstp) ++ (E-IfTrue :: big-to-small bstp₁)
-- big-to-small (E-IfFalse bstp bstp₁) = E-If* (big-to-small bstp) ++ (E-IfFalse :: big-to-small bstp₁)
-- big-to-small (E-IfErr bstp) = E-If* (big-to-small bstp) ++ [ E-If-Err ]
-- big-to-small {H1 = H1} {H2 = Cons v H2} (E-New bstp) = (E-New* (big-to-small bstp)) ++ [ E-NewVal refl ]
-- big-to-small (E-Deref bstp) = (E-Deref* (big-to-small bstp)) ++ [ E-DerefVal ]
-- big-to-small (E-DerefErr bstp) = (E-Deref* (big-to-small bstp)) ++ [ E-Deref-Err ]
-- big-to-small (E-Assign bstp) = (E-Assign* (big-to-small bstp)) ++ [ {!!} ] 
-- big-to-small (E-IsZeroZ bstp) = E-IsZero* (big-to-small bstp) ++ [ E-IsZeroZero ]
-- big-to-small (E-IsZeroS bstp) = E-IsZero* (big-to-small bstp) ++ [ E-IsZeroSucc ]

-- -- A value term evaluates to itself.
-- value-of-value : forall {ty n} {H : Heap n} -> (v : Value ty) -> BStep {H1 = H} {H2 = H} ⌜ v ⌝ v
-- value-of-value vtrue = E-True
-- value-of-value vfalse = E-False
-- value-of-value (vnat n) = E-Num
-- value-of-value (vref x) = E-Ref
-- value-of-value verror = E-Error

-- Combining a single small step with a big step.
-- prepend-step : forall {ty n1 n2 n3} {H1 : Heap n1} {H2 : Heap n2} {H3 : Heap n3} {t1 t2 : Term ty} {v : Value ty} -> 
--                Step {H1 = H1} {H2 = H2} t1 t2 -> BStep {H1 = H2} {H2 = H3} t2 v -> BStep {H1 = H1} {H2 = H3} t1 v
-- prepend-step E-IsZeroZero E-True = E-IsZeroZ E-Num
-- prepend-step E-IsZeroSucc E-False = E-IsZeroS E-Num
-- prepend-step (E-IsZero stp) (E-IsZeroZ bstp) = E-IsZeroZ (prepend-step stp bstp)
-- prepend-step (E-IsZero stp) (E-IsZeroS bstp) = E-IsZeroS (prepend-step stp bstp)
-- prepend-step E-IfTrue bstp = E-IfTrue E-True bstp
-- prepend-step E-IfFalse bstp = E-IfFalse E-False bstp
-- prepend-step (E-If stp) (E-IfTrue bstp bstp₁) = E-IfTrue (prepend-step stp bstp) bstp₁
-- prepend-step (E-If stp) (E-IfFalse bstp bstp₁) = E-IfFalse (prepend-step stp bstp) bstp₁
-- prepend-step (E-If stp) (E-IfErr bstp) = E-IfErr (prepend-step stp bstp)
-- prepend-step (E-New stp) (E-New bstp) = E-New (prepend-step stp bstp)
-- prepend-step (E-NewVal refl) E-Ref = E-New (value-of-value _)
-- prepend-step (E-Deref stp) (E-Deref bstp) = E-Deref (prepend-step stp bstp)
-- prepend-step (E-Deref stp) (E-DerefErr bstp) = E-DerefErr (prepend-step stp bstp)
-- prepend-step E-DerefVal bstp = {!!}
-- prepend-step (E-AssLeft stp) bstp = {!!}
-- prepend-step (E-AssRight isV stp) bstp = {!!}
-- prepend-step (E-Try-Catch stp) bstp = {!!}
-- prepend-step (E-Try-Catch-Suc x) bstp = {!!}
-- prepend-step (E-Try-Catch-Fail isE) bstp = {!!}
-- prepend-step E-IsZero-Err bstp = {!!}
-- prepend-step E-If-Err bstp = {!!}
-- prepend-step E-Deref-Err bstp = {!!}
-- prepend-step E-Assign-Err1 bstp = {!!}

-- small-to-big : ∀ {ty n m} {H1 : Heap n} {H2 : Heap m} {t : Term ty} {v : Value ty} → 
--                  Steps {H1 = H1} {H2 = H2} t ⌜ v ⌝ -> BStep {H1 = H1} {H2 = H2} t v
-- small-to-big [] = value-of-value _
-- small-to-big (stp :: stps) = prepend-step stp (small-to-big stps)
