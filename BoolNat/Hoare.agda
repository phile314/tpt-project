module Hoare where

open import Base hiding ( true ; false )
open import BigStep
open import Data.Sum
open import Data.Product
open import Data.Unit
open import Data.Empty renaming (⊥-elim to contradiction)
open import Data.Bool renaming ( _∧_ to _and_  ; _∨_ to _or_ )
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
p ∧ q = λ H -> p H and q H

-- Direct interpretation
_∨_ : Predicate -> Predicate -> Predicate
p ∨ q = \ H -> (p H) or (q H) 

-- Implies
_⇒_ : Predicate -> Predicate -> Predicate
p ⇒ q = \ H -> (not (p H)) or (q H) 

-- A direct encoding is more convinient. I wonder whether I would get the same with the derived operators.

-- Derived operators : 

-- -- Disjunction
-- _∨_ : Predicate -> Predicate -> Predicate
-- p ∨ q = ¬ ((¬ p) ∧ (¬ q))

-- -- Implies
-- _⇒_ : Predicate -> Predicate -> Predicate
-- p ⇒ q = (¬ p) ∨ q

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
postTrue validQ = λ _ _ → validQ

-- I don't know whether there is something from the standard library for this.
lemma : ∀ {p} -> T p -> T (not p) -> ⊥
lemma {true} p₁ p₂ = p₂
lemma {false} p₁ p₂ = p₁

-- If the precondition is always false in any state ( ⊧ (¬ P) ) then any program S and any post condition Q
-- form a valid hoare triple < P > S < Q > . The point is that Hoare triples have the premises that the precondition
-- holds. If this is not the case I do not have any obligation.
preFalse : ∀ {ty} {P Q : Predicate} {S : Term ty} ->  ⊧ (¬ P) -> < P > S < Q >
preFalse invalidP bstp P = contradiction (lemma P invalidP)

xor : ∀ p q -> T (p or q) -> (T p × T q) ⊎ ( T p ⊎ T q)
xor true true tpq = inj₁ (tt , tt)
xor true false tpq = inj₂ (inj₁ tt)
xor false true tpq = inj₂ (inj₂ tt)
xor false false () 

-- Precondition strengthening 
preStrength : ∀ {ty} {P P' Q : Predicate} {S : Term ty} ->
              ⊧ (P ⇒ P') -> < P' > S < Q > -> < P > S < Q >
preStrength {P = P} {P' = P'} p2p' triple {n} {m} {H1} with xor (not (P H1)) (P' H1) p2p'
preStrength p2p' triple | inj₁ (TP , TP') = λ bstp _ → triple bstp TP'
preStrength p2p' triple | inj₂ (inj₁ notTP) = λ bstp TP → contradiction (lemma TP notTP)
preStrength p2p' triple | inj₂ (inj₂ TP') = λ bstp _ → triple bstp TP'

