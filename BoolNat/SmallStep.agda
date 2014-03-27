module SmallStep where

open import BoolNat

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
 E-NewVal     : ∀ {ty S} {H : Heap S} {v : Term ty} {isV : isValue v} -> 
                Step (Allocate {v = v} {isV = isV} (Same H)) (new v) (ref (Top {S}))
 E-Deref      : ∀ {ty S1 S2 t t'} {s : S1 ⊆ S2} {H1 : Heap S1} {H2 : Heap S2} {δ : Δ s H1 H2} ->
                Step {Ref ty} δ t t' -> Step {ty} δ (! t) (! t')
 E-DerefVal   : forall {S S' H ty} {e : Elem S' ty} {isP : S' ⊆ S} {t : Term (Ref ty)} -> 
                Step {ty} (Same H) (! t) (lookup H (weaken isP e))
 E-AssLeft    : ∀ {ty S1 S2} {s : S1 ⊆ S2} {H1 : Heap S1} {H2 : Heap S2} {δ : Δ s H1 H2} {t1 t1' : Term (Ref ty)} {t2 : Term ty} ->
                Step {Ref ty} δ t1 t1' ->  Step {ty} δ (t1 <- t2) (t1' <- t2)
 E-AssRight   : ∀ {ty S1 S2} {s : S1 ⊆ S2} {H1 : Heap S1} {H2 : Heap S2} {δ : Δ s H1 H2} {v : Term (Ref ty)} {t t' : Term ty} 
                (isV : isValue v) -> Step δ t t' -> Step δ (v <- t) (v <- t')
 E-AssRed     : ∀ {ty S S'} {H : Heap S} {v : Term ty} {isV : isValue v} {e : Elem S' ty} {isP : S' ⊆ S} ->
                Step (Replace (weaken isP e) v {isV} (Same H)) ((ref e) <- v) v

-- You don't need this proof anymore, it's directly encoded in the Step
-- Proof that the shape only grows. Could be useful for proofs.
no-shrink :  ∀ {ty S1 S2} {H1 : Heap S1} {H2 : Heap S2} {s : S1 ⊆ S2} {t1 t2 : Term ty} {δ : Δ s H1 H2} 
             -> Step δ t1 t2 -> S1 ⊆ S2
no-shrink {s = s} stp = s
