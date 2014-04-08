module Hoare where

open import Base hiding ( true ; false )
open import BigStep
open import Denotational as D
open import Data.Nat
open import Data.Sum
open import Data.Product
open import Data.Unit
open import Data.Empty renaming (⊥-elim to contradiction)
open import Data.Bool hiding ( if_then_else_ ) renaming ( _∧_ to _and_  ; _∨_ to _or_ )
open import Function
open import Relation.Nullary renaming ( ¬_ to Not )
open import Relation.Binary.PropositionalEquality

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

-- A direct encoding is more convenient. I wonder whether I would get the same with the derived operators.

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
 
-- Lifts a boolean expression to a predicate
lift : Term Boolean -> Predicate
lift t H with ⟦ t ⟧ H 
lift t H | D.< vtrue , heap > = true
lift t H | D.< _ , heap > = false

-- Example
isEmpty : Predicate
isEmpty Nil = true
isEmpty (Cons v H) = false

------------------------------------------------------------------------------
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

-- An expression is a particular kind of term which does not affect the state (Heap)

isExpr : ∀ {ty} -> Term ty -> Set
isExpr Base.true = ⊤
isExpr Base.false = ⊤
isExpr error = ⊤
isExpr (num x) = ⊤
isExpr (iszero t) = isExpr t
isExpr (if t then t₁ else t₂) = (isExpr t × isExpr t₁ × isExpr t₂) 
isExpr (new t) = ⊥
isExpr (! t) = isExpr t
isExpr (t <- t₁) = ⊥
isExpr (ref x) = ⊤
isExpr (try t catch t₁) = (isExpr t) × (isExpr t₁)
isExpr (t >> t₁) = (isExpr t) × (isExpr t₁) 

-- examples
const-exprs : isExpr (Base.true)
const-exprs = tt

if-expr : isExpr (if Base.false then (num 1) else error)
if-expr = tt , tt , tt

-- non-expr : isExpr (! new Base.true)
-- non-expr = {!!}

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

split : ∀ p q -> T (p or q) -> (T p × T q) ⊎ ( T p ⊎ T q)
split true true tpq = inj₁ (tt , tt)
split true false tpq = inj₂ (inj₁ tt)
split false true tpq = inj₂ (inj₂ tt)
split false false () 

-- Precondition strengthening 
preStrength : ∀ {ty} {P P' Q : Predicate} {S : Term ty} ->
              ⊧ (P ⇒ P') -> < P' > S < Q > -> < P > S < Q >
preStrength {P = P} {P' = P'} p2p' triple {n} {m} {H1} with split (not (P H1)) (P' H1) p2p'
preStrength p2p' triple | inj₁ (TP , TP') = λ bstp _ → triple bstp TP'
preStrength p2p' triple | inj₂ (inj₁ notTP) = λ bstp TP → contradiction (lemma TP notTP)
preStrength p2p' triple | inj₂ (inj₂ TP') = λ bstp _ → triple bstp TP'


-- Postcondition weakening
postWeak : ∀ {ty} {P Q Q' : Predicate} {S : Term ty} ->
           ⊧ (Q' ⇒ Q) -> < P > S < Q' > -> < P > S < Q >
postWeak {P = P} {Q = Q} {Q' = Q'} qq triple {n} {m} {H1} {H2} with split (not (Q' H2)) (Q H2) qq 
postWeak qq triple | inj₁ (TNotQ' , TQ) = λ _ _ → TQ
postWeak qq triple | inj₂ (inj₁ TNotQ') = λ bstp TP → contradiction (lemma (triple bstp TP) TNotQ')
postWeak qq triple | inj₂ (inj₂ TQ) = λ _ _ → TQ

-- TODO : Import sound and complete from Proofs
⇓sound : ∀ {ty n m} {H1 : Heap n} {H2 : Heap m} (t : Term ty) (v : Value ty) -> 
         BStep {H1 = H1} {H2 = H2} t v -> ⟦ t ⟧ H1 ≡ D.< v , H2 >
⇓sound = {!!} 

⇓complete : ∀ {ty n} -> (t : Term ty) -> (H1 : Heap n) -> 
              let D.< v , H2 > = ⟦ t ⟧ H1 in BStep {H1 = H1} {H2 = H2} t v 
⇓complete = {!!}

lift-true : ∀ {n m} {H1 : Heap n} {H2 : Heap m} {c : Term Boolean} -> BStep {H1 = H1} {H2 = H2} c vtrue -> T (lift c H1) 
lift-true {H1 = H1} {c = c} bstp with ⟦ c ⟧ H1 | ⇓sound _ _ bstp
lift-true {n} {m} {H1} {H2} bstp | .(D.< vtrue , H2 >) | refl = tt

lift-false : ∀ {n m} {H1 : Heap n} {H2 : Heap m} {c : Term Boolean} -> BStep {H1 = H1} {H2 = H2} c vfalse -> T (not (lift c H1)) 
lift-false {H1 = H1} {c = c} bstp with ⟦ c ⟧ H1 | ⇓sound _ _ bstp
lift-false {n} {m} {H1} {H2} bstp | .(D.< vfalse , H2 >) | refl = tt

lift-err : ∀ {n m} {H1 : Heap n} {H2 : Heap m} {c : Term Boolean} -> BStep {H1 = H1} {H2 = H2} c verror -> T (not (lift c H1)) 
lift-err {H1 = H1} {c = c} bstp with ⟦ c ⟧ H1 | ⇓sound _ _ bstp
lift-err {n} {m} {H1} {H2} bstp | .(D.< verror , H2 >) | refl = tt


pack : ∀ {p q} -> T p -> T q -> T (p and q)
pack {true} {true} TP TQ = tt
pack {true} {false} TP ()
pack {false} {true} () TQ
pack {false} {false} () ()

-- I think that with our language this rule as it is does not hold.
-- The problem is that in our language expressions are statements (they can affect the state  / heap)
-- At the moment we are considering the Heap as a program State.
-- The problem is that evaluation can change the Heap.
-- Consider the Hoare Triple : < IsEmpty > if !(new true) then skip else skip < IsEmpty >
-- According to the if-rule it is valid if :
--     < IsEmpty ∧ ! ( new true ) > skip < IsEmpty >
--     < IsEmpty ^ ¬ ! ( new true ) > skip > < IsEmpty >
-- The first triple is invalid, but still is synatctically valid.

-- With this lemma I want to show that if an expression is big-step evaluated the heap does not change.
-- However I don't know how to type this lemma: ≡ does not work because the two heaps are different types
-- because n m are different. 
-- expr-lemma : ∀ {ty n m} -> {t : Term ty} {v : Value ty} {H1 : Heap m} {H2 : Heap n} (isE : isExpr t) ->
--              BStep {H1 = H1} {H2 = H2} t v -> H1 ≡ H2
-- expr-lemma = {!!}

-- Here I get the same error
-- expr-lemma : ∀ {ty n m} -> {t : Term ty} {H1 : Heap m} -> (isE : isExpr t) ->
--              let D.< v , H2 > = ⟦ t ⟧ H1 in H1 ≡ H2
-- expr-lemma = {!!}


hoare-if-expr : ∀ {ty} {P Q : Predicate} {c : Term Boolean} {isE : isExpr c} {S1 S2 : Term ty} ->
                < P ∧ (lift c) > S1 < Q > -> < P ∧ (¬ (lift c)) > S2 < Q > -> < P > if c then S1 else S2 < Q >
hoare-if-expr = {!!}

-- Provide a different if-rule :
-- Require :  ⊧ (P ∧ C ⇒ A) , ⊧ (P ∧ ¬ C ⇒ B) , < A > S1 < Q > ,  < B > S2 < Q >
-- I think this is what you would get if you would first evaluate c and then sequence it with the if (considering only the value)

-- hoare-if : ∀ {ty} {P Q : Predicate} {c : Term Boolean} {S1 S2 : Term ty} ->
--            < P ∧ (lift c) > S1 < Q > -> < P ∧ (¬ (lift c)) > S2 < Q > -> < P > if c then S1 else S2 < Q >
hoare-if : ∀ {ty} {P Q : Predicate} {c : Term Boolean} {S1 S2 : Term ty} ->
           < (\ H -> P H and lift c H )  > S1 < Q > -> < P ∧ (¬ (lift c)) > S2 < Q > -> < P > if c then S1 else S2 < Q >

hoare-if {c = c} triple-c triple-not-c {H1 = H1} (E-IfTrue {H3 = H3} bstp bstp₁) with ⟦ c ⟧ H1 | ⇓sound _ _ bstp
hoare-if triple-c triple-not-c {H1 = H1} (E-IfTrue {H3 = H3} bstp bstp₁) | D.< vtrue , H2 > | refl =  λ TP → triple-c {H1 = H2} {H2 = H3} bstp₁ (pack {!TP!} (lift-true bstp))
hoare-if triple-c triple-not-c (E-IfFalse bstp bstp₁) = {!!}
hoare-if triple-c triple-not-c (E-IfErr bstp) = {!!}

-- hoare-if {c = c} {S1} {S2} triple-c triple-not-c {n} {m} {H1} bstp TP with  ⟦ if c then S1 else S2 ⟧ H1 | ⇓sound _ _ bstp
-- hoare-if triple-c triple-not-c {n} {m} {H1} {H2} {v} (E-IfTrue bstp bstp₁) TP | D.< .v , .H2 > | refl = triple-c bstp₁ {!!}
-- hoare-if triple-c triple-not-c {n} {m} {H1} {H2} {v} (E-IfFalse bstp bstp₁) TP | D.< .v , .H2 > | refl = triple-not-c bstp₁ {!!}
-- hoare-if triple-c triple-not-c {n} {m} {H1} {H2} (E-IfErr bstp) TP | D.< .verror , .H2 > | refl = {!!}

-- Sequence rule for hoare triples
-- I think that this rule does not cope with "errors" and "exceptions" (which are expressed with if-then-else).
-- Probably we should restrict somehow the rule to non failing statements.
hoare-seq : ∀ {ty ty'} {P Q R : Predicate} {S1 : Term ty} {S2 : Term ty'} ->
            < P > S1 < Q > -> < Q > S2 < R > -> < P > S1 >> S2 < R >
hoare-seq pS1q qS2r (E-Seq x bstp bstp₁) TP = qS2r bstp₁ (pS1q bstp TP)
hoare-seq pS1q qS2r (E-Seq-Err bstp) TP = qS2r {!!} (pS1q bstp TP) 
