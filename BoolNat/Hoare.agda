module Hoare where

open import Base hiding ( true ; false )
open import BigStep
open import Data.Unit
open import Data.Empty renaming (⊥-elim to contradiction)
open import Data.Bool hiding ( _∨_ ) renaming ( _∧_ to _&&_ )
open import Data.Nat hiding (pred)
open import Function
open import Relation.Nullary renaming ( ¬_ to Not )

--------------------------------------------------------------------------------
-- Predicates and combinators
--------------------------------------------------------------------------------

Predicate : Set
Predicate = ∀ {n} -> Heap n -> Bool

-- The predicate that holds in any state
True : Predicate
True = const true

-- The predicate that never holds in any state
False : Predicate
False = const false

-- Negation
¬_ : Predicate -> Predicate
¬ p = λ H → not (p H)

-- Conjunction
_∧_ : Predicate -> Predicate -> Predicate
p ∧ q = λ H -> p H && q H

-- Derived operators : 

-- Disjunction
_∨_ : Predicate -> Predicate -> Predicate
p ∨ q = ¬ ((¬ p) ∧ (¬ q))

-- Implies
_⇒_ : Predicate -> Predicate -> Predicate
p ⇒ q = (¬ p) ∨ q

-- Valid 
⊧_ : Predicate -> Set
⊧ P = ∀ {n} -> {H : Heap n} -> T (P H) 
 
-- Example
isEmpty : Predicate
isEmpty Nil = true
isEmpty (Cons v H) = false

--------------------------------------------------------------------------------
-- Hoare triples
--------------------------------------------------------------------------------

-- Definition.
-- Exploting T only valid hoare triples can be constructed.
<_>_<_> : ∀ {ty} -> Predicate -> Term ty -> Predicate -> Set
<_>_<_> {ty} P S Q = ∀ {n m} -> {H1 : Heap n} {H2 : Heap m} {v : Value ty} ->
                     BStep {H1 = H1} {H2 = H2} S v -> T (P H1) -> T (Q H2)


-- Examples
trivial : ∀ {ty} {t : Term ty} -> < True > t < True >
trivial = λ {ty} {t} {n} {m} {H1} {H2} {v} _ _ → tt

-- An invalid hoare triple cannot be constructed
-- impossible : ∀ {ty} {t : Term ty} -> < True > t < False > 
-- impossible = {!!}

--------------------------------------------------------------------------------
-- Theorems
--------------------------------------------------------------------------------

-- If the post condition is valid (⊧ Q) then for any precondition P and any program S
-- the hoare triple < P > S < Q > holds.
postTrue : ∀ {ty} {P Q : Predicate} {S : Term ty} -> ⊧ Q -> < P > S < Q >
postTrue validQ = λ {n} {m} {H1} {H2} {v} _ _ → validQ

-- I don't know whether there is something from the standard library for this.
lemma : ∀ {p} -> T p -> T (not p) -> ⊥
lemma {true} p₁ p₂ = p₂
lemma {false} p₁ p₂ = p₁

preFalse : ∀ {ty} {P Q : Predicate} {S : Term ty} ->  ⊧ (¬ P) -> < P > S < Q >
preFalse invalidP bstp P = contradiction (lemma P invalidP)
