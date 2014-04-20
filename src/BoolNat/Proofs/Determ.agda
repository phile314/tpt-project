module Proofs.Determ where

open import Base
open import SmallStep
open import Data.Unit using (unit)
open import Data.Product using ( ∃ ; _,_)
open import Relation.Binary.PropositionalEquality hiding ( [_] )
open import Data.Empty renaming (⊥-elim to contradiction)
open import Proofs.Misc


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

