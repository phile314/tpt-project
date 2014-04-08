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
no-shrink (E-AssRed-Suc isV eq rep) = ≤′-refl
no-shrink (E-AssRed-Fail nr) = ≤′-refl
no-shrink (E-Try-Catch stp) = no-shrink stp
no-shrink (E-Try-Catch-Suc x) = ≤′-refl
no-shrink (E-Try-Catch-Fail isE) = ≤′-refl
no-shrink E-IsZero-Err = ≤′-refl
no-shrink E-If-Err = ≤′-refl
no-shrink E-Deref-Err = ≤′-refl
no-shrink E-Assign-Err1 = ≤′-refl
no-shrink (E-Seq1 stp) = no-shrink stp
no-shrink (E-SeqVal isV) = ≤′-refl
no-shrink E-Seq-Err = ≤′-refl

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
term2NF (t1 >> t2) () t' stp

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
isError2isValue (t1 >> t2) ()

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
deterministic (E-AssLeft s1) (E-AssRed-Suc isV eq rep) = contradiction (value2NF _ _ s1)
deterministic (E-AssLeft s1) (E-AssRed-Fail nr) = contradiction (value2NF _ _ s1)
deterministic (E-AssLeft s1) E-Assign-Err1 = contradiction (value2NF _ _ s1)
deterministic (E-AssRight (isV , notE) s1) (E-AssLeft s2) = contradiction (term2NF _ isV _ s2)
deterministic (E-AssRight isV s1) (E-AssRight isV₁ s2) rewrite deterministic s1 s2 = refl
deterministic (E-AssRight (isV , isE) s1) (E-AssRed-Suc _ refl rep) = contradiction (value2NF _ _ s1)
deterministic (E-AssRight isV' s1) (E-AssRed-Fail {isV = isV} nr) = contradiction (term2NF _ isV _ s1)
deterministic (E-AssRight (isV , notE) s1) E-Assign-Err1 = contradiction (notE unit)
deterministic (E-AssRed-Suc _ eq rep) (E-AssLeft s2) = contradiction (term2NF _ unit _ s2)
deterministic (E-AssRed-Suc isV refl rep) (E-AssRight (isV₁ , notE) s2) = contradiction (term2NF _ isV _ s2)
deterministic (E-AssRed-Suc _ eq rep) (E-AssRed-Suc _ eq₁ rep₁) = refl
deterministic (E-AssRed-Suc _ eq rep) (E-AssRed-Fail notRep) = contradiction (notRep rep)
deterministic (E-AssRed-Fail notRep) (E-AssLeft s2) = contradiction (value2NF _ _ s2)
deterministic (E-AssRed-Fail {isV = isV} notRep) (E-AssRight isV₁ s2) = contradiction (term2NF _ isV _ s2)
deterministic (E-AssRed-Fail notRep) (E-AssRed-Suc _ eq rep) = contradiction (notRep rep)
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
deterministic (E-Seq1 s) (E-Seq1 s2) rewrite deterministic s s2 = refl
deterministic (E-Seq1 s) (E-SeqVal x) = contradiction (term2NF _ (Data.Product.proj₁ x) _ s)
deterministic (E-Seq1 ()) E-Seq-Err
deterministic (E-SeqVal s) (E-Seq1 s2) = contradiction (term2NF _ (Data.Product.proj₁ s) _ s2)
deterministic (E-SeqVal s) (E-SeqVal x) = refl
deterministic (E-SeqVal (unit , proj₂)) E-Seq-Err = contradiction (proj₂ unit)
deterministic E-Seq-Err (E-Seq1 ())
deterministic E-Seq-Err (E-SeqVal (proj₁ , proj₂)) = contradiction (proj₂ unit)
deterministic E-Seq-Err E-Seq-Err = refl


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
⇓complete (t1 >> t2) H = {!!}

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
⇓sound {H1 = H1} {H2 = H2} .(! t) .(lookup r H2) (E-Deref {r = r} {t = t} bstp) with  ⟦ t ⟧ H1 | ⇓sound t (vref r) bstp
⇓sound .(! t) .(lookup r H2) (E-Deref {t = t} bstp) | < vref r , H2 > | refl = refl
⇓sound {H1 = H1} (! t) .verror (E-DerefErr bstp) with  ⟦ t ⟧ H1 | ⇓sound t verror bstp
⇓sound {H1 = H1} (! t) .verror (E-DerefErr bstp) | < verror , H2 > | refl = refl 
⇓sound {H1 = H1} (ref m <- t) ._ (E-Assign  bstp) with ⟦ t ⟧ H1 | ⇓sound t _ bstp 
⇓sound {ty} (ref m <- t) ._ (E-Assign bstp) | (< v , H2 >) | refl = {!!} -- E-AssRed comes here and makes things horrible
⇓sound .error .verror E-Error = refl
⇓sound (ref .m₁) (vref m₁) E-Ref = refl
⇓sound {H1 = H1} (t1 >> t2) v (E-Seq isG stp1 stp2) with ⟦ t1 ⟧ H1 | ⇓sound t1 _ stp1
⇓sound (t1 >> t2) v (E-Seq notE stp1 stp2) | < vtrue , H2 > | refl with ⟦ t2 ⟧ H2 | ⇓sound t2 _ stp2
⇓sound (t1 >> t2) v (E-Seq notE stp1 stp2) | < vtrue , H3 > | refl | < .v , H2 > | refl = refl
⇓sound (t1 >> t2) v (E-Seq notE stp1 stp2) | < vfalse , H2 > | refl with  ⟦ t2 ⟧ H2 | ⇓sound t2 _ stp2
⇓sound (t1 >> t2) v (E-Seq notE stp1 stp2) | < vfalse , H2 > | refl | < .v , H3 > | refl = refl
⇓sound (t1 >> t2) v (E-Seq notE stp1 stp2) | < vnat x , H2 > | refl with ⟦ t2 ⟧ H2 | ⇓sound t2 _ stp2
⇓sound (t1 >> t2) v (E-Seq notE stp1 stp2) | < vnat x , H2 > | refl | < .v , H3 > | refl = refl
⇓sound (t1 >> t2) v (E-Seq notE stp1 stp2) | < vref x , H2 > | refl with ⟦ t2 ⟧ H2 | ⇓sound t2 _ stp2
⇓sound (t1 >> t2) v (E-Seq notE stp1 stp2) | < vref x , H2 > | refl | < .v , H3 > | refl = refl
⇓sound (t1 >> t2) v (E-Seq notE stp1 stp2) | < verror , H2 > | refl = contradiction (notE unit)
⇓sound {H1 = H1} (t1 >> t2) .verror (E-Seq-Err bstp) with ⟦ t1 ⟧ H1 | ⇓sound t1 verror bstp
⇓sound (t1 >> t2) .verror (E-Seq-Err bstp) | < verror , H2 > | refl = refl

