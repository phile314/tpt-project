module Proofs.Complete where

open import Base
open import BigStep
open import Denotational
open import Data.Unit using (unit)
open import Data.Nat
open import Data.Sum
open import Relation.Binary.PropositionalEquality hiding ( [_] )
open import Data.Empty renaming (⊥-elim to contradiction)

⇓complete : ∀ {ty n} -> (t : Term ty) -> (H1 : Heap n) -> 
              let < v , H2 > = ⟦ t ⟧ H1 in BStep {H1 = H1} {H2 = H2} t v 
⇓complete true H = E-True
⇓complete false H = E-False
⇓complete error H = E-Error
⇓complete (num x) H = E-Num
⇓complete (iszero t) H with ⟦ t ⟧ H | ⇓complete t H
⇓complete (iszero t) H | < vnat zero , heap > | bstp = E-IsZerZ bstp
⇓complete (iszero t) H | < vnat (suc x) , heap > | bstp = E-IsZerS bstp
⇓complete (iszero t) H | < verror , heap > | bstp = E-IsZerErr bstp
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
⇓complete {ty} (t <- t₁) H | < vref x , H' > | bstp | < value , H'' > | bstep₁ with elem? H'' x ty
⇓complete (t <- t₁) H | < vref x , H' > | bstp | < value , H'' > | bstep₁ | inj₁ x₁ = E-Ass x₁ bstp bstep₁ 
⇓complete (t <- t₁) H | < vref x , H' > | bstp | < value , H'' > | bstep₁ | inj₂ y = E-AssOob y bstp bstep₁
⇓complete (t <- t₁) H | < verror , heap > | bstp = E-AssErr bstp
⇓complete (ref x) H = E-Ref
⇓complete (try t catch t₁) H with ⟦ t ⟧ H | ⇓complete t H  
⇓complete (try t catch t₁) H | < vtrue , heap > | bstp = E-TryCat (λ z → z) bstp
⇓complete (try t catch t₁) H | < vfalse , heap > | bstp = E-TryCat (λ z → z) bstp
⇓complete (try t catch t₁) H | < vnat x , heap > | bstp = E-TryCat (λ z → z) bstp
⇓complete (try t catch t₁) H | < vref x , heap > | bstp = E-TryCat (λ z → z) bstp
⇓complete (try t catch t₁) H | < verror , H' > | bstp with ⟦ t₁ ⟧ H' | ⇓complete t₁ H'
⇓complete (try t catch t₁) H | < verror , H' > | bstp | < value , heap > | bstp₁ = E-TryCatEx bstp bstp₁
⇓complete (t1 >> t2) H with ⟦ t1 ⟧ H | ⇓complete t1 H
⇓complete (t1 >> t2) H | < vtrue , heap > | bstp = E-Seq (λ z → z) bstp (⇓complete t2 heap)
⇓complete (t1 >> t2) H | < vfalse , heap > | bstp = E-Seq (λ z → z) bstp (⇓complete t2 heap)
⇓complete (t1 >> t2) H | < vnat x , heap > | bstp = E-Seq (λ z → z) bstp (⇓complete t2 heap)
⇓complete (t1 >> t2) H | < vref x , heap > | bstp = E-Seq (λ z → z) bstp (⇓complete t2 heap)
⇓complete (t1 >> t2) H | < verror , heap > | bstp = E-SeqErr bstp
