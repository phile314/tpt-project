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
no-shrink (E-AssRed-Suc eq rep) = ≤′-refl
no-shrink (E-AssRed-Fail nr) = ≤′-refl
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
value2NF (vnat x) t ()
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
deterministic (E-AssLeft s1) (E-AssRed-Suc eq rep) = contradiction (value2NF _ _ s1)
deterministic (E-AssLeft s1) (E-AssRed-Fail nr) = contradiction (value2NF _ _ s1)
deterministic (E-AssLeft s1) E-Assign-Err1 = contradiction (value2NF _ _ s1)
deterministic (E-AssRight (isV , notE) s1) (E-AssLeft s2) = contradiction (term2NF _ isV _ s2)
deterministic (E-AssRight isV s1) (E-AssRight isV₁ s2) rewrite deterministic s1 s2 = refl
deterministic (E-AssRight (isV , isE) s1) (E-AssRed-Suc refl rep) = contradiction (value2NF _ _ s1)
deterministic (E-AssRight isV' s1) (E-AssRed-Fail {isV = isV} nr) = contradiction (term2NF _ isV _ s1)
deterministic (E-AssRight (isV , notE) s1) E-Assign-Err1 = contradiction (notE unit)
deterministic (E-AssRed-Suc eq rep) (E-AssLeft s2) = contradiction (term2NF _ unit _ s2)
deterministic (E-AssRed-Suc {isV = isV} refl rep) (E-AssRight (isV₁ , notE) s2) = contradiction (term2NF _ isV _ s2)
deterministic (E-AssRed-Suc eq rep) (E-AssRed-Suc eq₁ rep₁) = refl
deterministic (E-AssRed-Suc eq rep) (E-AssRed-Fail notRep) = contradiction (notRep rep)
deterministic (E-AssRed-Fail notRep) (E-AssLeft s2) = contradiction (value2NF _ _ s2)
deterministic (E-AssRed-Fail {isV = isV} notRep) (E-AssRight isV₁ s2) = contradiction (term2NF _ isV _ s2)
deterministic (E-AssRed-Fail notRep) (E-AssRed-Suc eq rep) = contradiction (notRep rep)
deterministic (E-AssRed-Fail notRep) (E-AssRed-Fail notRep₁) = refl
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

-- A term is a redex if it can be reduced further
data Redex : ∀ {ty n} -> Term ty -> Heap n -> Set where
  Red : ∀ {ty n m} -> {H1 : Heap n} {t : Term ty} -> (H2 : Heap m) -> (t' : Term ty) ->
        Step {H1 = H1} {H2 = H2} t t' -> Redex t H1

-- Proof object that a term is a value
data Is-value : {ty : Type} -> Term ty → Set where
  is-value : {ty : Type} -> (v : Value ty) → Is-value ⌜ v ⌝


-- Progress and preservation
progress : ∀ {ty n} (H1 : Heap n) -> (t : Term ty) -> ((Is-value t) ⊎ Redex t H1)
progress H1 true = inj₁ (is-value vtrue)
progress H1 false = inj₁ (is-value vfalse)
progress H1 error = inj₁ (is-value verror)
progress H1 (num x) = inj₁ (is-value (vnat x))
progress H1 (iszero t) with progress H1 t
progress H1 (iszero .(num 0)) | inj₁ (is-value (vnat zero)) = inj₂ (Red H1 true E-IsZeroZero)
progress H1 (iszero .(num (suc x))) | inj₁ (is-value (vnat (suc x))) = inj₂ (Red H1 false E-IsZeroSucc)
progress H1 (iszero .error) | inj₁ (is-value verror) = inj₂ (Red H1 error E-IsZero-Err)
progress H1 (iszero t) | inj₂ (Red H2 t' x) = inj₂ (Red H2 (iszero t') (E-IsZero x))
progress H1 (if t then t₁ else t₂) with progress H1 t
progress H1 (if .true then t₁ else t₂) | inj₁ (is-value vtrue) = inj₂ (Red H1 t₁ E-IfTrue)
progress H1 (if .false then t₁ else t₂) | inj₁ (is-value vfalse) = inj₂ (Red H1 t₂ E-IfFalse)
progress H1 (if .error then t₁ else t₂) | inj₁ (is-value verror) = inj₂ (Red H1 error E-If-Err)
progress H1 (if t then t₁ else t₂) | inj₂ (Red H2 t' x) = inj₂ (Red H2 (if t' then t₁ else t₂) (E-If x))
progress H1 (new t) with progress H1 t
progress H1 (new .(⌜ v ⌝)) | inj₁ (is-value v) = inj₂ (Red (Cons v H1) (ref zero) (E-NewVal refl))
progress H1 (new t) | inj₂ (Red H2 t' x) = inj₂ (Red H2 (new t') (E-New x))
progress H1 (! t) with progress H1 t 
progress H1 (! .(ref x)) | inj₁ (is-value (vref x)) = inj₂ (Red H1 ⌜ lookup x H1 ⌝ E-DerefVal)
progress H1 (! .error) | inj₁ (is-value verror) = inj₂ (Red H1 error E-Deref-Err)
progress H1 (! t) | inj₂ (Red H2 t' x) = inj₂ (Red H2 (! t') (E-Deref x))
progress H1 (t <- t₁) = {!!}
progress H1 (ref x) = inj₁ (is-value (vref x))
progress H1 (try t catch t₁) with progress H1 t
progress H1 (try .error catch t₁) | inj₁ (is-value verror) = inj₂ (Red H1 t₁ (E-Try-Catch-Fail unit))
progress H1 (try .true catch t₁) | inj₁ (is-value vtrue) = inj₂ (Red H1 true (E-Try-Catch-Suc (unit , (λ x → x))))
progress H1 (try .false catch t₁) | inj₁ (is-value vfalse) = inj₂ (Red H1 false (E-Try-Catch-Suc (unit , (λ x → x))))
progress H1 (try .(num x) catch t₁) | inj₁ (is-value (vnat x)) = inj₂ (Red H1 (num x) (E-Try-Catch-Suc (unit , (λ x₁ → x₁))))
progress H1 (try .(ref x) catch t₁) | inj₁ (is-value (vref x)) = inj₂ (Red H1 (ref x) (E-Try-Catch-Suc (unit , (λ x₁ → x₁))))
progress H1 (try t catch t₁) | inj₂ (Red H2 t' x) = inj₂ (Red H2 (try t' catch t₁) (E-Try-Catch x))

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
termination H (new t) with termination H t
termination H (new t) | Halts v H2 xs = Halts (vref _) (Cons v H2) ((E-New* xs) ++ [ E-NewVal refl ])
termination H (! t) with termination H t
termination H (! t) | Halts (vref x) H2 xs = Halts (lookup x H2) H2 ((E-Deref* xs) ++ [ E-DerefVal ])
termination H (! t) | Halts verror H2 xs = Halts verror H2 ((E-Deref* xs) ++ [ E-Deref-Err ])
termination H (t <- t₁) = {!!}
termination H (ref x) = Halts (vref x) H []
termination H (try t catch t₁) with termination H t
termination H (try t catch t₁) | Halts verror H2 xs = prepend-steps (E-Try* xs ++ [ (E-Try-Catch-Fail unit) ]) (termination H2 t₁)
termination H (try t catch t₁) | Halts vtrue H2 xs = Halts vtrue H2 ((E-Try* xs) ++ [ E-Try-Catch-Suc (unit , (λ x → x)) ])
termination H (try t catch t₁) | Halts vfalse H2 xs = Halts vfalse H2 (E-Try* xs ++ [ E-Try-Catch-Suc (unit , (λ x → x)) ])
termination H (try t catch t₁) | Halts (vnat x) H2 xs = Halts (vnat x) H2 (E-Try* xs ++ [ E-Try-Catch-Suc (unit , (λ x → x)) ])
termination H (try t catch t₁) | Halts (vref x) H2 xs = Halts (vref x) H2 (E-Try* xs ++ [ E-Try-Catch-Suc (unit , (λ x → x)) ])

--------------------------------------------------------------------------------
-- Big step is Complete and Sound
--------------------------------------------------------------------------------

⇓complete : ∀ {ty n} -> (t : Term ty) -> (H1 : Heap n) -> 
              let < v , H2 > = ⟦ t ⟧ H1 in BStep {H1 = H1} {H2 = H2} t v 
⇓complete true H = E-True
⇓complete false H = E-False
⇓complete error H = E-Error
⇓complete (num x) H = E-Num
⇓complete (iszero t) H with ⟦ t ⟧ H | ⇓complete t H
⇓complete (iszero t) H | < vnat zero , heap > | bstp = E-IsZeroZ bstp
⇓complete (iszero t) H | < vnat (suc x) , heap > | bstp = E-IsZeroS bstp
⇓complete (iszero t) H | < verror , heap > | bstp = {!!}
⇓complete (if t then t₁ else t₂) H with ⟦ t ⟧ H | ⇓complete t H
⇓complete (if t then t₁ else t₂) H | < vtrue , heap > | bstp = E-IfTrue bstp (⇓complete t₁ heap)
⇓complete (if t then t₁ else t₂) H | < vfalse , heap > | bstp = E-IfFalse bstp (⇓complete t₂ heap)
⇓complete (if t then t₁ else t₂) H | < verror , heap > | bstp = E-IfErr bstp
⇓complete (new t) H with ⟦ t ⟧ H | ⇓complete t H 
⇓complete (new t) H | < value , heap > | bstp = E-New bstp
⇓complete (! t) H with ⟦ t ⟧ H | ⇓complete t H
⇓complete (! t) H | < vref x , heap > | bstp = E-Deref bstp
⇓complete (! t) H | < verror , heap > | bstp = E-DerefErr bstp
⇓complete (t <- t₁) H with ⟦ t ⟧ H | ⇓complete t H
⇓complete (t <- t₁) H | < vref x , H' > | bstp with ⟦ t₁ ⟧ H' | ⇓complete t₁ H'
⇓complete (t <- t₁) H | < vref x , H' > | bstp | < value , heap > | bstep₁ = {!!}
⇓complete (t <- t₁) H | < verror , heap > | bstp = {!!}
⇓complete (ref x) H = E-Ref
⇓complete (try t catch t₁) H with ⟦ t ⟧ H | ⇓complete t H  
⇓complete (try t catch t₁) H | < vtrue , heap > | bstp = {!!}
⇓complete (try t catch t₁) H | < vfalse , heap > | bstp = {!!}
⇓complete (try t catch t₁) H | < vnat x , heap > | bstp = {!!}
⇓complete (try t catch t₁) H | < vref x , heap > | bstp = {!!}
⇓complete (try t catch t₁) H | < verror , heap > | bstp = {!!}
⇓sound : ∀ {ty n m} {H1 : Heap n} {H2 : Heap m} (t : Term ty) (v : Value ty) -> 
         BStep {H1 = H1} {H2 = H2} t v -> ⟦ t ⟧ H1 ≡ < v , H2 >
⇓sound .true .vtrue E-True = refl
⇓sound .false .vfalse E-False = refl
⇓sound (num n) (vnat .n) E-Num = refl
⇓sound {H1 = H1} (iszero t) .vtrue (E-IsZeroZ bstp) with ⟦ t ⟧ H1 | ⇓sound t (vnat zero) bstp
⇓sound (iszero t) .vtrue (E-IsZeroZ bstp) | (< vnat 0 , H2 >) | refl = refl
⇓sound {H1 = H1} (iszero t) .vfalse (E-IsZeroS {n = n} bstp) with ⟦ t ⟧ H1 | ⇓sound t (vnat (suc n)) bstp
⇓sound (iszero t) .vfalse (E-IsZeroS bstp) | (< vnat (suc n₁) , H2 >) | refl = refl
⇓sound {H1 = H1} (if t then t1 else t2) v (E-IfTrue bstp bstp₁) with ⟦ t ⟧ H1 | ⇓sound t vtrue bstp
⇓sound (if t then t1 else t2) v (E-IfTrue bstp bstp₁) | < vtrue , H2 > | refl = ⇓sound t1 v bstp₁
⇓sound {H1 = H1} (if t then t1 else t2) v (E-IfFalse bstp bstp₁) with ⟦ t ⟧ H1 | ⇓sound t vfalse bstp 
⇓sound (if t then t1 else t2) v (E-IfFalse bstp bstp₁) | < vfalse , H2 > | refl = ⇓sound t2 v bstp₁
⇓sound {H1 = H1} (if t then t1 else t2) .verror (E-IfErr bstp) with ⟦ t ⟧ H1 | ⇓sound t verror bstp
⇓sound (if t then t1 else t2) .verror (E-IfErr bstp) | < verror , H2 > | refl = refl 
⇓sound {H1 = H1} (new t) (vref 0) (E-New bstp) with ⟦ t ⟧ H1 | ⇓sound t _ bstp
⇓sound (new t) (vref zero) (E-New bstp) | < v , H2 > | refl = refl 
⇓sound {ty} {n} {m} {H1} {H2} .(! t) .(lookup r H2) (E-Deref {.ty} {.n} {.m} {r} {.H1} {.H2} {t} bstp) with  ⟦ t ⟧ H1 | ⇓sound t (vref r) bstp
⇓sound {ty} {n} {m} {H1} {H2} .(! t) .(lookup r H2) (E-Deref {.ty} {.n} {.m} {r} {.H1} {.H2} {t} bstp) | .(< vref r , H2 >) | refl = refl
⇓sound {ty} {n} {m} {H1} {H2} (! t) .verror (E-DerefErr bstp) with  ⟦ t ⟧ H1 | ⇓sound t verror bstp
⇓sound {ty} {n} {m} {H1} {H2} (! t) .verror (E-DerefErr bstp) | .(< verror , H2 >) | refl = refl 
⇓sound {H1 = H1} (ref m <- t) ._ (E-Assign  bstp) with ⟦ t ⟧ H1 | ⇓sound t _ bstp 
⇓sound {ty} (ref m <- t) ._ (E-Assign bstp) | (< v , H2 >) | refl = {!!} -- E-AssRed comes here and makes things horrible
⇓sound .error .verror E-Error = refl
⇓sound (ref .m₁) (vref m₁) E-Ref = refl
