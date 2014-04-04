module SmallStep where

open import Base
open import Data.Nat renaming (ℕ to Nat) 
open import Data.Unit
open import Data.Fin

data Step : ∀ {ty n m} -> {H1 : Heap n} -> {H2 : Heap m} -> Term ty -> Term ty -> Set where
 E-IfTrue     : ∀ {ty S} {H : Heap S} {t1 t2 : Term ty} -> Step {H1 = H} {H2 = H} (if true  then t1 else t2) t1
 E-IfFalse    : ∀ {ty S} {H : Heap S} {t1 t2 : Term ty} -> Step {H1 = H} {H2 = H} (if false then t1 else t2) t2
 E-If         : ∀ {ty n m t1 t1'} {H1 : Heap n} {H2 : Heap m} {t2 t3 : Term ty} ->
                Step {H1 = H1} {H2 = H2} t1 t1' -> Step {H1 = H1} {H2 = H2}(if t1 then t2 else t3) (if t1' then t2 else t3)
 E-Succ       : ∀ {n m t t'} {H1 : Heap n} {H2 : Heap m} -> 
                Step {H1 = H1} {H2 = H2} t t' -> Step {H1 = H1} {H2 = H2} (succ t) (succ t')

 -- E-IsZeroZero : ∀ {S} {H : Heap S} -> Step (Same H) (iszero zero) true
 -- E-IsZeroSucc : ∀ {S t} {H : Heap S} -> isValue t -> Step (Same H) (iszero (succ t)) false
 -- E-IsZero     : ∀ {S1 S2 t t'} {s : S1 ⊆ S2} {H1 : Heap S1} {H2 : Heap S2} {δ : Δ s H1 H2} ->
 --                Step δ t t' -> Step δ (iszero t) (iszero t')
 E-New        : ∀ {ty n m t t'} {H1 : Heap n} {H2 : Heap m} ->
                Step {H1 = H1} {H2 = H2} t t' -> Step {Ref ty} {H1 = H1} {H2 = H2} (new t) (new t')
 E-NewVal     : ∀ {ty n} {H : Heap n} {v : Value ty} -> 
                Step {H1 = H} {H2 = Cons v H} (new ⌜ v ⌝) (ref 0) -- Note that since we Cons instead of append after every allocation references point to the wrong locations 
 E-Deref      : ∀ {ty S1 S2 t t'} {H1 : Heap S1} {H2 : Heap S2} ->
                Step {Ref ty} {H1 = H1} {H2 = H2} t t' -> Step{ty} {H1 = H1} {H2 = H2} (! t) (! t')
 E-DerefVal   : forall {ty n} {H : Heap n} {m : Nat} -> 
                Step {ty} {H1 = H} {H2 = H} (! (ref m)) (⌜ lookup m H ⌝)
 -- E-AssLeft    : ∀ {ty S1 S2} {s : S1 ⊆ S2} {H1 : Heap S1} {H2 : Heap S2} {δ : Δ s H1 H2} {t1 t1' : Term (Ref ty)} {t2 : Term ty} ->
 --                Step {Ref ty} δ t1 t1' ->  Step {ty} δ (t1 <- t2) (t1' <- t2)
 -- E-AssRight   : ∀ {ty S1 S2} {s : S1 ⊆ S2} {H1 : Heap S1} {H2 : Heap S2} {δ : Δ s H1 H2} {v : Term (Ref ty)} {t t' : Term ty} 
 --                (isV : isValue v) -> Step δ t t' -> Step δ (v <- t) (v <- t')
 E-AssRed     : ∀ {ty} {v : Value ty} {n : Nat} {H : Heap n} {p : Replace H ty} ->
                Step {H1 = H} {H2 = replace v H p} ((ref n) <- ⌜ v ⌝) ⌜ v ⌝
 -- The only step available when the replace cannot be executed
 E-AssFail    : ∀ {ty n m} ->  {v : Value ty} {H : Heap n} -> Step {H1 = H} {H2 = H} ((ref m) <- ⌜ v ⌝ ) error


 
 -- Here we need to add all the "failing" rules such as 
 E-If-Err     : ∀ {ty n} {H : Heap n} {t1 t2 : Term ty} -> Step {H1 = H} {H2 = H} (if error then t1 else t2) error
-- E-IsZero-Err
-- E-AssLeft-Err
-- E-AssRight-Err
-- ...

-- Sequence of steps
data Steps : ∀ {ty n m} -> {H1 : Heap n} -> {H2 : Heap m} -> Term ty -> Term ty -> Set where
  [] : ∀ {ty n} {H : Heap n} {t : Term ty} -> Steps {H1 = H} {H2 = H} t t
  _::_ : ∀ {ty n₁ n₂ n₃} {t₁ t₂ t₃ : Term ty} {H1 : Heap n₁} {H2 : Heap n₂} {H3 : Heap n₃} -> 
         Step {H1 = H1} {H2 = H2} t₁ t₂ -> Steps {H1 = H2} {H2 = H3} t₂ t₃ ->
         Steps {H1 = H1} {H2 = H3} t₁ t₃
       
_++_ : ∀ {ty n₁ n₂ n₃} {t₁ t₂ t₃ : Term ty} {H1 : Heap n₁} {H2 : Heap n₂} {H3 : Heap n₃} -> 
         Steps {H1 = H1} {H2 = H2} t₁ t₂ -> Steps {H1 = H2} {H2 = H3} t₂ t₃ -> 
         Steps {H1 = H1} {H2 = H3} t₁ t₃
[] ++ ys = ys
(x :: xs) ++ ys = x :: (xs ++ ys)

[_] : ∀ {ty n m} {H1 : Heap n} {H2 : Heap m} {t1 t2 : Term ty} -> Step {H1 = H1} {H2 = H2} t1 t2 -> Steps {H1 = H1} {H2 = H2} t1 t2
[ stp ] = stp :: []

