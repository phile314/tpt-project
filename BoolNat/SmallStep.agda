module SmallStep where

open import Base
open import Data.Nat renaming (ℕ to Nat) 
open import Data.Maybe
open import Data.Unit
open import Data.Product
open import Data.Fin
open import Relation.Nullary.Core

try-replace : ∀ {ty n} {H : Heap n} -> Value ty -> ((Heap n) × (Value ty))
try-replace {ty} {n} {H} v with replace? H n ty
try-replace {ty} {n} {H} v | just x = ( replace v H x , v )
try-replace {ty} {n} {H} v | nothing = H , verror

data Step : ∀ {ty n m} -> {H1 : Heap n} -> {H2 : Heap m} -> Term ty -> Term ty -> Set where
 E-Succ       : ∀ {n m t t'} {H1 : Heap n} {H2 : Heap m} -> 
                Step {H1 = H1} {H2 = H2} t t' -> Step {H1 = H1} {H2 = H2} (succ t) (succ t')



 E-IsZeroZero : ∀ {n} {H : Heap n} -> Step {H1 = H} {H2 = H} (iszero zero) true
 E-IsZeroSucc : ∀ {n} {H : Heap n} {t : Term Natural} -> isValue t -> Step {H1 = H} {H2 = H} (iszero (succ t)) false
 E-IsZero     : ∀ {n m} {H1 : Heap n} {H2 : Heap m} {t t' : Term Natural} ->
                Step {H1 = H1} {H2 = H2} t t' -> Step {H1 = H1} {H2 = H2} (iszero t) (iszero t')

 E-IfTrue     : ∀ {ty S} {H : Heap S} {t1 t2 : Term ty} -> Step {H1 = H} {H2 = H} (if true  then t1 else t2) t1
 E-IfFalse    : ∀ {ty S} {H : Heap S} {t1 t2 : Term ty} -> Step {H1 = H} {H2 = H} (if false then t1 else t2) t2
 E-If         : ∀ {ty n m t1 t1'} {H1 : Heap n} {H2 : Heap m} {t2 t3 : Term ty} ->
                Step {H1 = H1} {H2 = H2} t1 t1' -> Step {H1 = H1} {H2 = H2}(if t1 then t2 else t3) (if t1' then t2 else t3)



 E-New        : ∀ {ty n m t t'} {H1 : Heap n} {H2 : Heap m} ->
                Step {H1 = H1} {H2 = H2} t t' -> Step {Ref ty} {H1 = H1} {H2 = H2} (new t) (new t')
 E-NewVal     : ∀ {ty n} {H : Heap n} {v : Value ty} ->
                Step {H1 = H} {H2 = Cons v H} (new ⌜ v ⌝) (ref 0) -- Note that since we Cons instead of append after every allocation references point to the wrong locations 
 E-Deref      : ∀ {ty S1 S2 t t'} {H1 : Heap S1} {H2 : Heap S2} ->
                Step {Ref ty} {H1 = H1} {H2 = H2} t t' -> Step{ty} {H1 = H1} {H2 = H2} (! t) (! t')
 E-DerefVal   : forall {ty n} {H : Heap n} {m : Nat} -> 
                Step {ty} {H1 = H} {H2 = H} (! (ref m)) (⌜ lookup m H ⌝)

 E-AssLeft    : ∀ {ty n m} {H1 : Heap n} {H2 : Heap m} {t1 t1' : Term (Ref ty)} {t2 : Term ty} ->
                Step {H1 = H1} {H2 = H2} t1 t1' ->  Step {H1 = H1} {H2 = H2} (t1 <- t2) (t1' <- t2)
 E-AssRight   : ∀ {ty n m} {H1 : Heap n} {H2 : Heap m} {v : Term (Ref ty)} {t t' : Term ty}
                (isV : isValue v) -> Step {H1 = H1} {H2 = H2} t t' -> Step {H1 = H1} {H2 = H2} (v <- t) (v <- t')

 E-AssRed     : ∀ {ty n r} {v : Value ty} {H1 H2 : Heap n} ->
                Step {H1 = H1} {H2 = proj₁ (try-replace {H = H1} v)} ((ref r) <- ⌜ v ⌝) ⌜ (proj₂ (try-replace {H = H1} v)) ⌝





 E-Try-Catch  : ∀ {ty n m} {H1 : Heap n} {H2 : Heap m} -> {t t' tc : Term ty} ->
                Step {H1 = H1} {H2 = H2} t t' -> Step {H1 = H1} {H2 = H2} (try t catch tc) (try t' catch tc)
 E-Try-Catch-Suc  : ∀ {ty n} {H : Heap n} {t tc : Term ty} ->
                    isGoodValue t -> Step {H1 = H} {H2 = H} (try t catch tc) t
 E-Try-Catch-Fail : ∀ {ty n} {H : Heap n} {tc : Term ty} ->
                    Step {H1 = H} {H2 = H} (try error catch tc) tc
 
 -- Here we need to add all the "failing" rules such as 
 E-Succ-Err   : ∀ {n} {H : Heap n} -> Step {H1 = H} {H2 = H} (succ error) error
 E-IsZero-Err : ∀ {n} {H : Heap n} -> Step {H1 = H} {H2 = H} (iszero error) error
 E-If-Err     : ∀ {ty n} {H : Heap n} {t1 t2 : Term ty} -> Step {H1 = H} {H2 = H} (if error then t1 else t2) error
 E-Deref-Err  : ∀ {ty n} {H : Heap n} -> Step {H1 = H} {H2 = H} (!_ {ty} error) error
 E-Assign-Err1 : ∀ {ty n} {H : Heap n} {t : Term ty} -> Step {H1 = H} {H2 = H} (error <- t) error
 -- We dont need this rule because rrrors can be stored in the heap
-- E-Assign-Err2 : ∀ {ty n} {H : Heap n} {t : Term (Ref ty)} -> Step {H1 = H} {H2 = H} (t <- error) error
 

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

