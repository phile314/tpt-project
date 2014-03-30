module SmallStep where

open import BoolNat
open import Data.Sum
open import Data.Product
open import Data.Unit
open import Relation.Binary.PropositionalEquality

data Step : forall {ty S1 S2} -> {H1 : Heap S1} -> {H2 : Heap S2} -> {s : S1 ⊆ S2} -> Δ s H1 H2 -> Term ty -> Term ty -> Set where
 E-IfTrue     : ∀ {ty S} {H : Heap S} {t1 t2 : Term ty} -> Step (Same H) (if true  then t1 else t2) t1
 E-IfFalse    : ∀ {ty S} {H : Heap S} {t1 t2 : Term ty} -> Step (Same H) (if false then t1 else t2) t2
 E-If         : ∀ {ty S1 S2 t1 t1'} {s : S1 ⊆ S2} {H1 : Heap S1} {H2 : Heap S2} {δ : Δ s H1 H2} {t2 t3 : Term ty} ->
                Step δ t1 t1' -> Step δ (if t1 then t2 else t3) (if t1' then t2 else t3)
 E-Succ       : ∀ {S1 S2 t t'} {s : S1 ⊆ S2} {H1 : Heap S1} {H2 : Heap S2} {δ : Δ s H1 H2} -> 
                Step {Natural} δ t  t' -> Step δ (succ t) (succ t')
 E-IsZeroZero : ∀ {S} {H : Heap S} -> Step (Same H) (iszero zero) true
 E-IsZeroSucc : ∀ {S t} {H : Heap S} -> isValue t -> Step (Same H) (iszero (succ t)) false
 E-IsZero     : ∀ {S1 S2 t t'} {s : S1 ⊆ S2} {H1 : Heap S1} {H2 : Heap S2} {δ : Δ s H1 H2} ->
                Step δ t t' -> Step δ (iszero t) (iszero t')
 E-New        : ∀ {ty S1 S2 t t'} {s : S1 ⊆ S2} {H1 : Heap S1} {H2 : Heap S2} {δ : Δ s H1 H2} ->
                Step δ t t' -> Step {Ref ty} δ (new t) (new t')
 E-NewVal     : ∀ {ty S} {H : Heap S} {v : Value ty} -> 
                Step (Allocate v (Same H)) (new ⌜ v ⌝) (ref (Top {S}))
 E-Deref      : ∀ {ty S1 S2 t t'} {s : S1 ⊆ S2} {H1 : Heap S1} {H2 : Heap S2} {δ : Δ s H1 H2} ->
                Step {Ref ty} δ t t' -> Step {ty} δ (! t) (! t')
 E-DerefVal   : forall {S S' H ty} {e : Elem S' ty} {isP : S' ⊆ S} {t : Term (Ref ty)} -> 
                Step {ty} (Same H) (! t) (⌜ lookup H (weaken isP e) ⌝)
 E-AssLeft    : ∀ {ty S1 S2} {s : S1 ⊆ S2} {H1 : Heap S1} {H2 : Heap S2} {δ : Δ s H1 H2} {t1 t1' : Term (Ref ty)} {t2 : Term ty} ->
                Step {Ref ty} δ t1 t1' ->  Step {ty} δ (t1 <- t2) (t1' <- t2)
 E-AssRight   : ∀ {ty S1 S2} {s : S1 ⊆ S2} {H1 : Heap S1} {H2 : Heap S2} {δ : Δ s H1 H2} {v : Term (Ref ty)} {t t' : Term ty} 
                (isV : isValue v) -> Step δ t t' -> Step δ (v <- t) (v <- t')
 E-AssRed     : ∀ {ty S S'} {H : Heap S} {v : Value ty} {e : Elem S' ty} {isP : S' ⊆ S} ->
                Step (Replace (weaken isP e) v (Same H)) ((ref e) <- ⌜ v ⌝) ⌜ v ⌝

-- You don't need this proof anymore, it's directly encoded in the Step
-- Proof that the shape only grows. Could be useful for proofs.
no-shrink :  ∀ {ty S1 S2} {H1 : Heap S1} {H2 : Heap S2} {s : S1 ⊆ S2} {t1 t2 : Term ty} {δ : Δ s H1 H2} 
             -> Step δ t1 t2 -> S1 ⊆ S2
no-shrink {s = s} stp = s


-- Progress and preservation
--progress : forall {d} -> {ty : Type} -> (t : Term ty) -> ((isValue t) ⊎ (∃ (Step d t)))
progress : {S1 S2 : Shape} -> {s1 : S1 ⊆ S2 } {H1 : Heap S1} {H2 : Heap S2} {δ : Δ s1 H1 H2} {ty : Type} -> (t : Term ty) -> ((isValue t) ⊎ (∃ (Step δ t)))
progress true = inj₁ unit
progress false = inj₁ unit
progress zero = inj₁ unit
progress {S1} {S2} {s1} {H1} {H2} {ty} (succ t) with progress {S1} {S2} {s1} {H1} {H2} {ty} t
progress (succ t) | inj₁ x = inj₁ x -- TODO shouldn't this be (succ t)?
progress (succ t) | inj₂ (proj₁ , proj₂) = inj₂ ((succ proj₁) , (E-Succ proj₂))
progress {S1} {S2} {s1} {H1} {H2} {ty} (iszero t) with progress {S1} {S2} {s1} {H1} {H2} {ty} t
progress (iszero zero) | inj₁ x = inj₂ (true , {!E-IsZeroZero !})
progress {S1} {S2} {s1} {H1} {H2} (iszero (succ t)) | inj₁ x = {!!} -- inj₂ (false , {!!})
progress (iszero (if t then t₁ else t₂)) | inj₁ ()
progress (iszero (! t)) | inj₁ ()
progress (iszero (t <- t₁)) | inj₁ ()
progress (iszero t) | inj₂ (proj₁ , proj₂) = inj₂ (iszero proj₁ , E-IsZero proj₂)
progress (if t then t₁ else t₂) = {!!}
progress {S1} {S2} {s1} {H1} {H2} {ty} (new t) with progress {S1} {S2} {s1} {H1} {H2} {ty} t
progress (new t) | inj₁ x = inj₂ (ref {!!} , {!E-NewVal!})
progress (new t) | inj₂ (proj₁ , proj₂) = inj₂ ((new proj₁) , (E-New proj₂))
progress {S1} {S2} {s1} {H1} {H2} {ty} (! t) with progress {S1} {S2} {s1} {H1} {H2} {ty} t
progress (! (if t then t₁ else t₂)) | inj₁ ()
progress (! new t) | inj₁ ()
progress (! (! t)) | inj₁ ()
progress (! (t <- t₁)) | inj₁ ()
progress {S1} {S2} {s1} {H1} {H2} (! ref x) | inj₁ unit = inj₂ (( ⌜ lookup H1 ((weaken {!!} x)) ⌝ ) , {!E-DerefVal!}) -- we cannot use E-DerefVal here for some reason. Why? (Mismatching Heaps/Shapes?)
progress (! t) | inj₂ (proj₁ , proj₂) = inj₂ (! proj₁ , E-Deref proj₂)
progress (t <- t₁) = {!!}
progress (ref e) = {!!}

preservation : {S1 S2 : Shape} {s1 : S1 ⊆ S2 } {H1 : Heap S1} {H2 : Heap S2} {δ : Δ s1 H1 H2} {ty : Type} {t : Term ty} {t' : Term ty} -> Step δ t t' -> ty ≡ ty
preservation stp = refl

