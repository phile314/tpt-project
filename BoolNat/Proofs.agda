-- This module contains the metatheories proved for the language

module Proofs where

open import Base
open import SmallStep
open import BigStep
open import Denotational
open import Data.Unit using (unit)
open import Data.Sum
open import Data.Product using ( ∃ ; _,_)
open import Data.Nat 
open import Relation.Binary.PropositionalEquality hiding ( [_] )
open import Relation.Nullary
open import Data.Empty renaming (⊥-elim to contradiction)

-- Proof that the heap only grows.
no-shrink :  ∀ {ty n m} {H1 : Heap n} {H2 : Heap m} {t1 t2 : Term ty} -> Step {H1 = H1} {H2 = H2} t1 t2 -> n ≤′ m
no-shrink E-IsZeroZero = ≤′-refl
no-shrink E-IsZeroSucc = ≤′-refl
no-shrink (E-IsZero stp) = no-shrink stp
no-shrink E-IfTrue = ≤′-refl
no-shrink E-IfFalse = ≤′-refl
no-shrink (E-If stp) = no-shrink stp
no-shrink (E-New stp) = no-shrink stp
no-shrink (E-NewVal isV) = ≤′-step ≤′-refl
no-shrink (E-Deref stp) = no-shrink stp
no-shrink E-DerefVal = ≤′-refl
no-shrink (E-AssLeft stp) = no-shrink stp
no-shrink (E-AssRight isV stp) = no-shrink stp
no-shrink E-AssRed = ≤′-refl
no-shrink (E-Try-Catch stp) = no-shrink stp
no-shrink (E-Try-Catch-Suc x) = ≤′-refl
no-shrink (E-Try-Catch-Fail isE) = ≤′-refl
no-shrink E-IsZero-Err = ≤′-refl
no-shrink E-If-Err = ≤′-refl
no-shrink E-Deref-Err = ≤′-refl
no-shrink E-Assign-Err1 = ≤′-refl

-- A term is considered a normal form whenever it is not reducible.
NF : {ty : Type} -> Term ty → Set
NF {ty} t = ∀ {n m} {H1 : Heap n} {H2 : Heap m} (t' : Term ty) -> ¬ (Step {H1 = H1} {H2 = H2} t t')

term2NF : ∀ {ty} -> (t : Term ty) -> isValue t -> NF t
term2NF true isV t' ()
term2NF false isV t' ()
term2NF (num _) isV t' ()
term2NF error isV t' ()
term2NF (iszero t) () t' stp
term2NF (if t then t₁ else t₂) () t' stp
term2NF (new t) () t' stp
term2NF (! t) () t' stp
term2NF (t <- t₁) () t' stp
term2NF (ref x) isV t' ()
term2NF (try t catch t₁) () t' stp

value2NF : ∀ {ty} -> (v : Value ty) -> NF ⌜ v ⌝
value2NF vtrue t ()
value2NF vfalse t ()
value2NF (vnat x) t ()  -- Here stp should be an absurd pattern
value2NF (vref x) t ()
value2NF verror t ()

isError2isValue : ∀ {ty} -> (t : Term ty) -> isError t -> isValue t
isError2isValue true ()
isError2isValue false ()
isError2isValue (num _) ()
isError2isValue error isE = unit
isError2isValue (iszero t) ()
isError2isValue (if t then t₁ else t₂) ()
isError2isValue (new t) ()
isError2isValue (! t) ()
isError2isValue (t <- t₁) ()
isError2isValue (ref x) ()
isError2isValue (try t catch t₁) ()

deterministic : ∀ {ty n m1 m2} {H : Heap n} {H1 : Heap m1} {H2 : Heap m2} {t t1 t2 : Term ty} ->
                Step {H1 = H} {H2 = H1} t t1 -> Step {H1 = H} {H2 = H2} t t2 -> t1 ≡ t2
deterministic E-IsZeroZero E-IsZeroZero = refl
deterministic E-IsZeroZero (E-IsZero ())
deterministic E-IsZeroSucc E-IsZeroSucc = refl
deterministic E-IsZeroSucc (E-IsZero s2) = contradiction (term2NF _ unit _ s2)
deterministic (E-IsZero ()) E-IsZeroZero
deterministic (E-IsZero s1) E-IsZeroSucc = contradiction (term2NF _ unit _ s1)
deterministic (E-IsZero s1) (E-IsZero s2) rewrite deterministic s1 s2 = refl
deterministic (E-IsZero ()) E-IsZero-Err
deterministic E-IfTrue E-IfTrue = refl
deterministic E-IfTrue (E-If ())
deterministic E-IfFalse E-IfFalse = refl
deterministic E-IfFalse (E-If ())
deterministic (E-If ()) E-IfTrue
deterministic (E-If ()) E-IfFalse
deterministic (E-If s1) (E-If s2) rewrite deterministic s1 s2 = refl
deterministic (E-If ()) E-If-Err
deterministic (E-New s1) (E-New s2) rewrite deterministic s1 s2 = refl
deterministic (E-New s1) (E-NewVal refl) = contradiction (value2NF _ _ s1)
deterministic (E-NewVal refl) (E-New s2) = contradiction (value2NF _ _ s2)
deterministic (E-NewVal isV) (E-NewVal isV₁) = refl
deterministic (E-Deref s1) (E-Deref s2) rewrite deterministic s1 s2 = refl
deterministic (E-Deref ()) E-DerefVal
deterministic (E-Deref ()) E-Deref-Err
deterministic E-DerefVal (E-Deref ())
deterministic E-DerefVal E-DerefVal = refl
deterministic (E-AssLeft s1) (E-AssLeft s2) rewrite deterministic s1 s2 = refl
deterministic (E-AssLeft s1) (E-AssRight (isV , notE) s2) = contradiction (term2NF _ isV _ s1)
deterministic (E-AssLeft ()) E-AssRed
deterministic (E-AssLeft ()) E-Assign-Err1
deterministic (E-AssRight (isV , notE) s1) (E-AssLeft s2) = contradiction (term2NF _ isV _ s2)
deterministic (E-AssRight isV s1) (E-AssRight isV₁ s2) rewrite deterministic s1 s2 = refl
deterministic (E-AssRight isV s1) (E-AssRed {v = v}) = contradiction (value2NF v _ s1) -- Probably we should define E-AssRed differently
deterministic (E-AssRight (isV , notE) s1) E-Assign-Err1 = contradiction (notE unit) 
deterministic E-AssRed s2 = {!!} -- Probably we should define E-AssRed differently
deterministic (E-Try-Catch s1) (E-Try-Catch s2) rewrite deterministic s1 s2 = refl
deterministic (E-Try-Catch s1) (E-Try-Catch-Suc (isV , proj₂)) = contradiction (term2NF _ isV _ s1)
deterministic (E-Try-Catch s1) (E-Try-Catch-Fail isE) = contradiction (term2NF _ (isError2isValue _ isE) _ s1)
deterministic (E-Try-Catch-Suc (isV , proj₂)) (E-Try-Catch s2) = contradiction (term2NF _ isV _ s2)
deterministic (E-Try-Catch-Suc x) (E-Try-Catch-Suc x₁) = refl
deterministic (E-Try-Catch-Suc (isV , notE)) (E-Try-Catch-Fail isE) = contradiction (notE isE)
deterministic (E-Try-Catch-Fail isE) (E-Try-Catch s2) = contradiction (term2NF _ (isError2isValue _ isE) _ s2)
deterministic (E-Try-Catch-Fail isE) (E-Try-Catch-Suc (isV , notE)) = contradiction (notE isE)
deterministic (E-Try-Catch-Fail isE) (E-Try-Catch-Fail isE₁) = refl
deterministic E-IsZero-Err (E-IsZero ())
deterministic E-IsZero-Err E-IsZero-Err = refl
deterministic E-If-Err (E-If ())
deterministic E-If-Err E-If-Err = refl
deterministic E-Deref-Err (E-Deref ())
deterministic E-Deref-Err E-Deref-Err = refl
deterministic E-Assign-Err1 (E-AssLeft ())
deterministic E-Assign-Err1 (E-AssRight (isV , notE) stp) = contradiction (notE unit)
deterministic E-Assign-Err1 E-Assign-Err1 = refl

-- Progress and preservation
progress : ∀ {ty n m} {H1 : Heap n} {H2 : Heap m} -> (t : Term ty) -> ((isValue t) ⊎ (∃ (Step {H1 = H1} {H2 = H2} t)))
progress true = inj₁ unit
progress false = inj₁ unit
progress error = inj₁ unit
progress (num n) = inj₁ unit
progress (iszero t) = {!!}
progress (if t then t₁ else t₂) = {!!}
progress (new t) = {!!}
progress (! t) = {!!}
progress (t <- t₁) with progress t | progress t₁
progress (t <- t₁) | inj₁ x | inj₁ x₁ = inj₂ {!!}
progress (t <- t₁) | inj₁ x | inj₂ y = {!!}
progress (t <- t₁) | inj₂ y | inj₁ x = {!!}
progress (t <- t₁) | inj₂ y | inj₂ y₁ = {!!}
progress (ref x) = {!!}
progress (try t catch t₁) = {!!} 

preservation : ∀ {ty n m} {H1 : Heap n} {H2 : Heap m} {t : Term ty} {t' : Term ty} -> Step {H1 = H1} {H2 = H2} t t' -> ty ≡ ty
preservation stp = refl

--------------------------------------------------------------------------------
-- Termination
--------------------------------------------------------------------------------

-- With this formulation we cannot write the lemma prepend-steps.
-- I don't know whether inlining it would work.
-- I don't know if using another specific constructor would be better

data ⊢_↓_ {n : ℕ} {ty : Type} (H : Heap n) (t : Term ty) : Set where
  Halts : ∀ {m} (v : Value ty) -> (H2 : Heap m) -> Steps {H1 = H} {H2 = H2} t ⌜ v ⌝ -> ⊢ H ↓ t

prepend-steps : ∀ {ty n m} {H1 : Heap n} {H2 : Heap m} {t1 t2 : Term ty} -> Steps {H1 = H1} {H2 = H2} t1 t2  -> ⊢ H2 ↓ t2 -> ⊢ H1 ↓ t1
prepend-steps xs (Halts v H2 ys) = Halts v H2 (xs ++ ys)

termination : ∀ {ty n} -> (H : Heap n) -> (t : Term ty) -> ⊢ H ↓ t  
termination H true = Halts vtrue H []
termination H false = Halts vfalse H []
termination H error = Halts verror H []
termination H (num n) = Halts (vnat n) H []
termination H (iszero t) with termination H t
termination H (iszero t) | Halts (vnat zero) H2 xs = Halts vtrue H2 ((E-IsZero* xs) ++ [ E-IsZeroZero ])
termination H (iszero t) | Halts (vnat (suc x)) H2 xs = Halts vfalse H2 ((E-IsZero* xs) ++ [ E-IsZeroSucc ])
termination H (iszero t) | Halts verror H2 xs = Halts verror H2 ((E-IsZero* xs) ++ [ E-IsZero-Err ])
termination H (if t then t₁ else t₂) with termination H t
termination H (if t then t₁ else t₂) | Halts vtrue H2 xs = prepend-steps (E-If* xs ++ [ E-IfTrue ]) (termination H2 t₁)
termination H (if t then t₁ else t₂) | Halts vfalse H2 xs = prepend-steps ((E-If* xs) ++ [ E-IfFalse ]) (termination H2 t₂)
termination H (if t then t₁ else t₂) | Halts verror H2 xs = Halts verror H2 ((E-If* xs) ++ [ E-If-Err ])
termination H (new t) = {!!}
termination H (! t) = {!!}
termination H (t <- t₁) = {!!}
termination H (ref x) = {!!}
termination H (try t catch t₁) with termination H t
termination H (try t catch t₁) | Halts verror H2 xs = prepend-steps (E-Try* xs ++ [ (E-Try-Catch-Fail unit) ]) (termination H2 t₁)
termination H (try t catch t₁) | Halts vtrue H2 xs = Halts vtrue H2 ((E-Try* xs) ++ [ E-Try-Catch-Suc (unit , (λ x → x)) ])
termination H (try t catch t₁) | Halts vfalse H2 xs = Halts vfalse H2 (E-Try* xs ++ [ E-Try-Catch-Suc (unit , (λ x → x)) ])
termination H (try t catch t₁) | Halts (vnat x) H2 xs = Halts (vnat x) H2 (E-Try* xs ++ [ E-Try-Catch-Suc (unit , (λ x → x)) ])
termination H (try t catch t₁) | Halts (vref x) H2 xs = Halts (vref x) H2 (E-Try* xs ++ [ E-Try-Catch-Suc (unit , (λ x → x)) ])

--------------------------------------------------------------------------------
-- Big step is Complete and Sound
--------------------------------------------------------------------------------

-- Not completely sure if the definitions are correct and if they will work out

⇓complete' : ∀ {ty n m} {H1 : Heap n} {H2 : Heap m} (t : Term ty) (v : Value ty) ->
             ⟦ t ⟧ H1 ≡ < v , H2 > -> BStep {H1 = H1} {H2 = H2} t v
⇓complete' true vtrue refl = E-True
⇓complete' false .vfalse refl = E-False
⇓complete' (num n) .(vnat n) refl = E-Num
⇓complete' error .verror refl = E-Error
⇓complete' {H1 = H1} (iszero t) v p with ⟦ t ⟧ H1 
⇓complete' {.Boolean} {n} {m} {H1} {H2} (iszero t) .vtrue refl | < vnat zero , .H2 > = {!!}
⇓complete' {.Boolean} {n} {m} {H1} {H2} (iszero t) .vfalse refl | < vnat (suc x) , .H2 > = {!!}
⇓complete' {.Boolean} {n} {m} {H1} {H2} (iszero t) .verror refl | < verror , .H2 > = {!!}
⇓complete' {H1 = H1} (if t then t₁ else t₂) v p with ⟦ t ⟧ H1
⇓complete' (if t then t₁ else t₂) v p | < vtrue , H1' > with ⟦ t₁ ⟧ H1'
⇓complete' {ty} {n₁} {m} {H1} {H2} (if t then t₁ else t₂) v refl | < vtrue , H1' > | < .v , .H2 > = E-IfTrue {H1 = H1} {H2 = H2} (⇓complete' t vtrue {!!}) (⇓complete' t₁ v {!!})
⇓complete' {H1 = H1} (if t then t₁ else t₂) v p | < vfalse , H1' > with ⟦ t₂ ⟧ H1'
⇓complete' {ty} {n₁} {m} {H1} {H2} (if t then t₁ else t₂) v refl | < vfalse , H1' > | < .v , .H2 > = E-IfFalse {H1 = H1} {H2 = H2} (⇓complete' t vfalse {!!})  (⇓complete' t₂ v {!!}) 
⇓complete' (if t then t₁ else t₂) v p | < verror , H1' > = {!!}
⇓complete' {H1 = H1} (new t) v p with ⟦ t ⟧ H1
⇓complete' (new t) .(vref 0) refl | < v , H1' > = E-New (⇓complete' t v {!!})
⇓complete' {H1 = H1} (! t) v p with ⟦ t ⟧ H1
⇓complete' {ty} {n} {m} {H1} {H2} (! t) .(lookup x H2) refl | < vref x , .H2 > = {!E-Deref ? !} -- The E-Deref rule requires the two heaps to be the same, but in general they are the same. This problems comes down to an inconvenient formulation (we don't want to specify the second heap 
⇓complete' {ty} {n} {m} {H1} {H2} (! t) .verror refl | < verror , .H2 > = {!!}
⇓complete' {H1 = H1} (t <- t₁) v p with ⟦ t ⟧ H1
⇓complete' (t <- t₁) v p | < vref n , H1' > with ⟦ t₁ ⟧ H1'
⇓complete' (t <- t₁) v p | < vref n₃ , H1' > | < vtrue , H2' > = {!!}  -- AssRed is to complicated
⇓complete' (t <- t₁) v p | < vref n₃ , H1' > | < vfalse , H2' > = {!!}
⇓complete' (t <- t₁) v p | < vref n₃ , H1' > | < vnat x , H2' > = {!!}
⇓complete' (t <- t₁) v p | < vref n₃ , H1' > | < vref x , H2' > = {!!}
⇓complete' (t <- t₁) v p | < vref n₃ , H1' > | < verror , H2' > = {!!}
⇓complete' {ty} {n} {m} {H1} {H2} (t <- t₁) .verror refl | < verror , .H2 > = {!!}
⇓complete' (ref x) .(vref x) refl = E-Ref
⇓complete' {H1 = H1} (try t catch t₁) v p with ⟦ t ⟧ H1
⇓complete' (try t catch t₁) v p | < verror , x₁ > = {!!}
⇓complete' (try t catch t₁) v p | < v' , x₁ > = {!!}

⇓complete : ∀ {ty n} {H1 : Heap n} (t : Term ty) -> BStep {H1 = H1} {H2 = {!!}} t (value (⟦ t ⟧ H1)) 
⇓complete = {!!}



⇓sound : ∀ {ty n m} {H1 : Heap n} {H2 : Heap m} (t : Term ty) (v : Value ty) -> 
         BStep {H1 = H1} {H2 = H2} t v -> ⟦ t ⟧ H1 ≡ < v , H2 >
⇓sound .true .vtrue E-True = refl
⇓sound .false .vfalse E-False = refl
⇓sound (num n) (vnat .n) E-Num = refl
⇓sound {H1 = H1} (if t then t1 else t2) v (E-IfTrue bstp bstp₁) with ⟦ t ⟧ H1 | ⇓sound t vtrue bstp
⇓sound (if t then t1 else t2) v (E-IfTrue bstp bstp₁) | < vtrue , H2 > | refl = ⇓sound t1 v bstp₁
⇓sound {H1 = H1} (if t then t1 else t2) v (E-IfFalse bstp bstp₁) with ⟦ t ⟧ H1 | ⇓sound t vfalse bstp 
⇓sound (if t then t1 else t2) v (E-IfFalse bstp bstp₁) | < vfalse , H2 > | refl = ⇓sound t2 v bstp₁
⇓sound {H1 = H1} (new t) (vref 0) (E-New bstp) with ⟦ t ⟧ H1 | ⇓sound t _ bstp
⇓sound (new t) (vref zero) (E-New bstp) | < v , H2 > | refl = refl 
⇓sound {ty} {.m} {m} {.H2} {H2} .(! t) .(lookup r H2) (E-Deref {.ty} {.m} {r} {.H2} {t} bstp) with  ⟦ t ⟧ H2 | ⇓sound t (vref r) bstp
⇓sound {ty} {.m} {m} {.H2} {H2} .(! t) .(lookup r H2) (E-Deref {.ty} {.m} {r} {.H2} {t} bstp) | .(< vref r , H2 >) | refl = refl
⇓sound {H1 = H1} (ref m <- t) ._ (E-Assign  bstp) with ⟦ t ⟧ H1 | ⇓sound t _ bstp 
⇓sound {ty} (ref m <- t) ._ (E-Assign bstp) | (< v , H2 >) | refl = {!!} -- E-AssRed comes here and makes things horrible
⇓sound .error .verror E-Error = refl
⇓sound (ref .m₁) (vref m₁) E-Ref = refl
