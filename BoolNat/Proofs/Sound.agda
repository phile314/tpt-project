module Proofs.Sound where

open import Base
open import BigStep
open import Denotational
open import Data.Unit using (unit)
open import Data.Nat
open import Data.Sum
open import Relation.Binary.PropositionalEquality hiding ( [_] )
open import Data.Empty renaming (⊥-elim to contradiction)

⇓sound : ∀ {ty n m} {H1 : Heap n} {H2 : Heap m} (t : Term ty) (v : Value ty) -> 
         BStep {H1 = H1} {H2 = H2} t v -> ⟦ t ⟧ H1 ≡ < v , H2 >
⇓sound .true     .vtrue     E-True            = refl
⇓sound .false    .vfalse    E-False           = refl
⇓sound .(num m₁) .(vnat m₁) (E-Num {._} {m₁}) = refl
⇓sound .(ref m₁) .(vref m₁) (E-Ref {._} {m₁}) = refl
⇓sound .error    .verror    E-Error           = refl
⇓sound {H1 = H1} (if t then t1 else t2) v (E-IfTrue bstp bstp₁) with ⟦ t ⟧ H1 | ⇓sound t vtrue bstp
⇓sound (if t then t1 else t2) v (E-IfTrue bstp bstp₁) | < vtrue , H2 > | refl = ⇓sound t1 v bstp₁
⇓sound {H1 = H1} (if t then t1 else t2) v (E-IfFalse bstp bstp₁) with ⟦ t ⟧ H1 | ⇓sound t vfalse bstp 
⇓sound (if t then t1 else t2) v (E-IfFalse bstp bstp₁) | < vfalse , H2 > | refl = ⇓sound t2 v bstp₁
⇓sound {H1 = H1} (if t then t1 else t2) .verror (E-IfErr bstp) with ⟦ t ⟧ H1 | ⇓sound t verror bstp
⇓sound (if t then t1 else t2) .verror (E-IfErr bstp) | < verror , H2 > | refl = refl 
⇓sound {H1 = H1} (iszero t) .vtrue (E-IsZerZ bstp) with ⟦ t ⟧ H1 | ⇓sound t (vnat zero) bstp
⇓sound (iszero t) .vtrue (E-IsZerZ bstp) | (< vnat 0 , H2 >) | refl = refl
⇓sound {H1 = H1} (iszero t) .vfalse (E-IsZerS {n = n} bstp) with ⟦ t ⟧ H1 | ⇓sound t (vnat (suc n)) bstp
⇓sound (iszero t) .vfalse (E-IsZerS bstp) | (< vnat (suc n₁) , H2 >) | refl = refl
⇓sound {H1 = H1} (iszero t) .verror (E-IsZerErr b) with ⟦ t ⟧ H1        | ⇓sound t verror b
... | .(< verror , _ >) | refl = refl
⇓sound {H1 = H1} (new t) (vref n) (E-New bstp) with ⟦ t ⟧ H1 | ⇓sound t _ bstp
⇓sound (new t) (vref n) (E-New bstp) | < v , H2 > | refl = refl 
⇓sound {H1 = H1} {H2 = H2} .(! t) .(lookup r H2) (E-Deref {r = r} {t = t} bstp) with  ⟦ t ⟧ H1 | ⇓sound t (vref r) bstp
⇓sound .(! t) .(lookup r H2) (E-Deref {t = t} bstp) | < vref r , H2 > | refl = refl
⇓sound {H1 = H1} (! t) .verror (E-DerefErr bstp) with  ⟦ t ⟧ H1 | ⇓sound t verror bstp
⇓sound {H1 = H1} (! t) .verror (E-DerefErr bstp) | < verror , H2 > | refl = refl 

⇓sound (t1 <- t2) v (E-Ass  rep bstp bstp₁) = {!!}

⇓sound (t1 <- t2) .verror (E-AssOob x bstp bstp₁) = {!!}
⇓sound (t1 <- t2) .verror (E-AssErr bstp) = {!!}

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
⇓sound {H1 = H1} (t1 >> t2) .verror (E-SeqErr bstp) with ⟦ t1 ⟧ H1 | ⇓sound t1 verror bstp
⇓sound (t1 >> t2) .verror (E-SeqErr bstp) | < verror , H2 > | refl = refl
⇓sound                    {H1 = H1} (try t1 catch t2) v        (E-TryCat a b) with ⟦ t1 ⟧ H1       | ⇓sound t1 v b
⇓sound {.Boolean} {n} {m} {H1} {H2} (try t1 catch t2) vtrue    (E-TryCat a b) | .(< vtrue  , H2 >) | refl          = refl
⇓sound {.Boolean} {n} {m} {H1} {H2} (try t1 catch t2) vfalse   (E-TryCat a b) | .(< vfalse , H2 >) | refl          = refl
⇓sound {.Natural} {n} {m} {H1} {H2} (try t1 catch t2) (vnat x) (E-TryCat a b) | .(< vnat x , H2 >) | refl          = refl
⇓sound {.(Ref _)} {n} {m} {H1} {H2} (try t1 catch t2) (vref x) (E-TryCat a b) | .(< vref x , H2 >) | refl          = refl
⇓sound {ty      } {n} {m} {H1} {H2} (try t1 catch t2) verror   (E-TryCat a b) | .(< verror , H2 >) | refl          = contradiction (a unit)
⇓sound {H1 = H1} (try t1 catch t2) v (E-TryCatEx bstp1 bspt2) with ⟦ t1 ⟧ H1 | ⇓sound t1 verror bstp1
⇓sound (try t1 catch t2) v (E-TryCatEx bstp1 bstp2) | < verror , H2 > | refl = ⇓sound t2 v bstp2
