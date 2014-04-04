module SmallStep where

open import BoolNat
open import Data.Nat renaming (ℕ to Nat) 
open import Data.Sum
open import Data.Product
open import Data.Unit
open import Data.Fin
open import Relation.Binary.PropositionalEquality

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
                Step {H1 = H} {H2 = Cons v H} (new ⌜ v ⌝) (ref n) -- Note that since we Cons instead of append after every allocation references point to the wrong locations 
 E-Deref      : ∀ {ty S1 S2 t t'} {H1 : Heap S1} {H2 : Heap S2} ->
                Step {Ref ty} {H1 = H1} {H2 = H2} t t' -> Step{ty} {H1 = H1} {H2 = H2} (! t) (! t')
 E-DerefVal   : forall {ty n} {H : Heap n} {m : Nat} -> 
                Step {ty} {H1 = H} {H2 = H} (! (ref m)) (⌜ lookup H m ⌝)
 -- E-AssLeft    : ∀ {ty S1 S2} {s : S1 ⊆ S2} {H1 : Heap S1} {H2 : Heap S2} {δ : Δ s H1 H2} {t1 t1' : Term (Ref ty)} {t2 : Term ty} ->
 --                Step {Ref ty} δ t1 t1' ->  Step {ty} δ (t1 <- t2) (t1' <- t2)
 -- E-AssRight   : ∀ {ty S1 S2} {s : S1 ⊆ S2} {H1 : Heap S1} {H2 : Heap S2} {δ : Δ s H1 H2} {v : Term (Ref ty)} {t t' : Term ty} 
 --                (isV : isValue v) -> Step δ t t' -> Step δ (v <- t) (v <- t')
 E-AssRed     : ∀ {ty} {v : Value ty} {n : Nat} {H : Heap (suc n)} {p : ty ≡ lookupTy (fromℕ n) H} ->
                Step {H1 = H} {H2 = replace v (fromℕ n) H p} ((ref n) <- ⌜ v ⌝) ⌜ v ⌝

 
 -- Here we need to add all the "failing" rules such as 
 E-If-Err     : ∀ {ty n} {H : Heap n} {t1 t2 : Term ty} -> Step {H1 = H} {H2 = H} (if error then t1 else t2) error
-- E-IsZero-Err
-- E-AssLeft-Err
-- E-AssRight-Err
-- ...

-- I think it will be lengthy but easy.
-- Proof that the shape only grows. Could be useful for proofs.
-- no-shrink :  ∀ {ty S1 S2} {H1 : Heap S1} {H2 : Heap S2} {s : S1 ⊆ S2} {t1 t2 : Term ty} {δ : Δ s H1 H2} 
--              -> Step δ t1 t2 -> S1 ⊆ S2
-- no-shrink {s = s} stp = s


-- Progress and preservation
--progress : forall {d} -> {ty : Type} -> (t : Term ty) -> ((isValue t) ⊎ (∃ (Step d t)))
-- progress : {S1 S2 : Shape} -> {s1 : S1 ⊆ S2 } {H1 : Heap S1} {H2 : Heap S2} {δ : Δ s1 H1 H2} {ty : Type} -> (t : Term ty) -> ((isValue t) ⊎ (∃ (Step δ t)))
-- progress true = inj₁ unit
-- progress false = inj₁ unit
-- progress zero = inj₁ unit
-- progress {S1} {S2} {s1} {H1} {H2} {ty} (succ t) with progress {S1} {S2} {s1} {H1} {H2} {ty} t
-- progress (succ t) | inj₁ x = inj₁ x -- TODO shouldn't this be (succ t)?
-- progress (succ t) | inj₂ (proj₁ , proj₂) = inj₂ ((succ proj₁) , (E-Succ proj₂))
-- progress {S1} {S2} {s1} {H1} {H2} {ty} (iszero t) with progress {S1} {S2} {s1} {H1} {H2} {ty} t
-- progress (iszero zero) | inj₁ x = inj₂ (true , {!E-IsZeroZero !})
-- progress {S1} {S2} {s1} {H1} {H2} (iszero (succ t)) | inj₁ x = {!!} -- inj₂ (false , {!!})
-- progress (iszero (if t then t₁ else t₂)) | inj₁ ()
-- progress (iszero (! t)) | inj₁ ()
-- progress (iszero (t <- t₁)) | inj₁ ()
-- progress (iszero error) | inj₁ p  = {!!} 
-- progress (iszero t) | inj₂ (proj₁ , proj₂) = inj₂ (iszero proj₁ , E-IsZero proj₂)
-- progress (if t then t₁ else t₂) = {!!}
-- progress {S1} {S2} {s1} {H1} {H2} {ty} (new t) with progress {S1} {S2} {s1} {H1} {H2} {ty} t
-- progress (new t) | inj₁ x = inj₂ (ref {!!} , {!E-NewVal!})
-- progress (new t) | inj₂ (proj₁ , proj₂) = inj₂ ((new proj₁) , (E-New proj₂))
-- progress {S1} {S2} {s1} {H1} {H2} {ty} (! t) with progress {S1} {S2} {s1} {H1} {H2} {ty} t
-- progress (! error) | inj₁ p = {!!}
-- progress (! (if t then t₁ else t₂)) | inj₁ ()
-- progress (! new t) | inj₁ ()
-- progress (! (! t)) | inj₁ ()
-- progress (! (t <- t₁)) | inj₁ ()
-- progress {S1} {S2} {s1} {H1} {H2} (! ref x) | inj₁ unit = inj₂ (( ⌜ lookup H1 {!!} ⌝ ) , {!E-DerefVal!}) -- we cannot use E-DerefVal here for some reason. Why? (Mismatching Heaps/Shapes?)
-- progress (! t) | inj₂ (proj₁ , proj₂) = inj₂ (! proj₁ , E-Deref proj₂)
-- progress (t <- t₁) = {!!}
-- progress (ref e) = {!!}
-- progress error = {!!}

preservation : ∀ {ty n m} {H1 : Heap n} {H2 : Heap m} {t : Term ty} {t' : Term ty} -> Step {H1 = H1} {H2 = H2} t t' -> ty ≡ ty
preservation stp = refl

