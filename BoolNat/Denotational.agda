module Denotational where

open import BoolNat
open import Data.Nat

------------------------------------------------------------------------
-- Denotational semantics.

-- Evaluation of if-then-else expressions applied to values.
cond : ∀ {ty} -> Value Boolean → Value ty → Value ty → Value ty
cond vtrue t e = t
cond vfalse t e = e

-- Evaluation function.
⟦_⟧ : {ty : Type} -> Term ty → Value ty
⟦ true ⟧ = vtrue
⟦ false ⟧ = vfalse
⟦ if c then t else e ⟧ = cond ⟦ c ⟧ ⟦ t ⟧ ⟦ e ⟧ 
⟦ zero ⟧ = vzero
⟦ succ t ⟧ = vsucc ⟦ t ⟧
⟦ iszero t ⟧ with ⟦ t ⟧
⟦ iszero t ⟧ | vzero = vtrue
⟦ iszero t ⟧ | vsucc n = vfalse
⟦ new t ⟧ = {!!}
⟦ ! t ⟧ = {!!}
⟦ t <- t₁ ⟧ = {!!}
⟦ ref ⟧ = {!!}
