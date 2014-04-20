module Proofs.ProgPres where

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
open import Data.Empty


-- A term is a redex if it can be reduced further
data Redex : ∀ {ty n} -> Term ty -> Heap n -> Set where
  Red : ∀ {ty n m} -> {H1 : Heap n} {t : Term ty} -> (H2 : Heap m) -> (t' : Term ty) ->
        Step {H1 = H1} {H2 = H2} t t' -> Redex t H1

-- Proof object that a term is a value
data Is-value : {ty : Type} -> Term ty → Set where
  is-value : {ty : Type} -> (v : Value ty) → Is-value ⌜ v ⌝

err? : ∀ {ty} {t : Term ty} -> (isV : Is-value t) -> (isError t ⊎ ¬ (isError t))
err? (is-value vtrue) = inj₂ (λ x → x)
err? (is-value vfalse) = inj₂ (λ x → x)
err? (is-value (vnat x)) = inj₂ (λ x₁ → x₁)
err? (is-value (vref x)) = inj₂ (λ x₁ → x₁)
err? (is-value verror) = inj₁ unit

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
progress {n = n} H1 (new .(⌜ v ⌝)) | inj₁ (is-value v) = inj₂ (Red (append H1 v) (ref n) (E-NewVal refl))
progress H1 (new t) | inj₂ (Red H2 t' x) = inj₂ (Red H2 (new t') (E-New x))
progress H1 (! t) with progress H1 t 
progress H1 (! .(ref x)) | inj₁ (is-value (vref x)) = inj₂ (Red H1 ⌜ lookup x H1 ⌝ E-DerefVal)
progress H1 (! .error) | inj₁ (is-value verror) = inj₂ (Red H1 error E-Deref-Err)
progress H1 (! t) | inj₂ (Red H2 t' x) = inj₂ (Red H2 (! t') (E-Deref x))
progress H1 (t <- t₁) with progress H1 t
progress H1 (.(⌜ v ⌝) <- t₁) | inj₁ (is-value v) with progress H1 t₁
progress {ty} H1 (.(⌜ v₁ ⌝) <- .(⌜ v ⌝)) | inj₁ (is-value v₁) | inj₁ (is-value v) with v₁
progress {ty} H1 (.(⌜ v₁ ⌝) <- .(⌜ v ⌝)) | inj₁ (is-value v₁) | inj₁ (is-value v) | vref x with elem? H1 x ty
progress {ty} H1 (.(⌜ v₁ ⌝) <- .(⌜ v ⌝)) | inj₁ (is-value v₁) | inj₁ (is-value v) | vref x | inj₁ x₁ = inj₂ (Red (replace H1 x₁ v) ⌜ v ⌝ (E-AssRed-Suc {ty} {_} {x} {H1} (isValue? v) refl x₁))
progress {ty} H1 (.(⌜ v₁ ⌝) <- .(⌜ v ⌝)) | inj₁ (is-value v₁) | inj₁ (is-value v) | vref x | inj₂ y = inj₂ (Red H1 error (E-AssRed-Fail {ty} {_} {x} {_} {isValue? v} y))
progress H1 (.(⌜ v₁ ⌝) <- .(⌜ v ⌝)) | inj₁ (is-value v₁) | inj₁ (is-value v) | verror = inj₂ (Red H1 error E-Assign-Err1)
progress H1 (.(⌜ vref x₁ ⌝) <- t₁) | inj₁ (is-value (vref x₁)) | inj₂ (Red H2 t' x) = inj₂ (Red H2 (ref x₁ <- t') (E-AssRight (unit , (λ x₂ → x₂)) x))
progress H1 (.(⌜ verror ⌝) <- t₁) | inj₁ (is-value verror) | inj₂ (Red H2 t' x) = inj₂ (Red H1 error E-Assign-Err1)
progress H1 (t <- t₁) | inj₂ (Red H2 t' x) = inj₂ (Red H2 (t' <- t₁) (E-AssLeft x))
progress H1 (ref x) = inj₁ (is-value (vref x))
progress H1 (try t catch t₁) with progress H1 t
progress H1 (try .error catch t₁) | inj₁ (is-value verror) = inj₂ (Red H1 t₁ (E-Try-Catch-Fail unit))
progress H1 (try .true catch t₁) | inj₁ (is-value vtrue) = inj₂ (Red H1 true (E-Try-Catch-Suc (unit , (λ x → x))))
progress H1 (try .false catch t₁) | inj₁ (is-value vfalse) = inj₂ (Red H1 false (E-Try-Catch-Suc (unit , (λ x → x))))
progress H1 (try .(num x) catch t₁) | inj₁ (is-value (vnat x)) = inj₂ (Red H1 (num x) (E-Try-Catch-Suc (unit , (λ x₁ → x₁))))
progress H1 (try .(ref x) catch t₁) | inj₁ (is-value (vref x)) = inj₂ (Red H1 (ref x) (E-Try-Catch-Suc (unit , (λ x₁ → x₁))))
progress H1 (try t catch t₁) | inj₂ (Red H2 t' x) = inj₂ (Red H2 (try t' catch t₁) (E-Try-Catch x))
progress H1 (t1 >> t2) with progress H1 t1
progress H1 (t1 >> t2) | inj₁ x with err? x
progress H1 (.true >> t2) | inj₁ (is-value vtrue) | inj₁ ()
progress H1 (.false >> t2) | inj₁ (is-value vfalse) | inj₁ ()
progress H1 (.(num x) >> t2) | inj₁ (is-value (vnat x)) | inj₁ ()
progress H1 (.(ref x) >> t2) | inj₁ (is-value (vref x)) | inj₁ ()
progress H1 (.error >> t2) | inj₁ (is-value verror) | inj₁ x₁ = inj₂ (Red H1 error E-Seq-Err)
progress H1 (.(⌜ v ⌝) >> t2) | inj₁ (is-value v) | inj₂ y = inj₂ (Red H1 t2 (E-SeqVal ((isValue? v) , y)))
progress H1 (t1 >> t2) | inj₂ (Red H2 t' x) = inj₂ (Red H2 (t' >> t2) (E-Seq1 x))

preservation : ∀ {ty n m} {H1 : Heap n} {H2 : Heap m} {t : Term ty} {t' : Term ty} -> Step {H1 = H1} {H2 = H2} t t' -> ty ≡ ty
preservation stp = refl

