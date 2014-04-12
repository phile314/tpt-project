module Hoare where

open import Base hiding ( true ; false )
open import BigStep
open import Denotational as D
open import Data.Nat
open import Data.Sum
open import Data.Product
open import Data.Unit
open import Data.Empty
open import Data.Bool hiding ( if_then_else_ ) renaming ( _∧_ to _and_  ; _∨_ to _or_ )
open import Function
open import Relation.Nullary renaming ( ¬_ to Not )
open import Relation.Binary.PropositionalEquality

-- TODO move all the examples to another module
-- TODO : Import sound from Proofs
⇓sound : ∀ {ty n m} {H1 : Heap n} {H2 : Heap m} (t : Term ty) (v : Value ty) -> 
         BStep {H1 = H1} {H2 = H2} t v -> ⟦ t ⟧ H1 ≡ D.< v , H2 >
⇓sound = {!!} 

--------------------------------------------------------------------------------
-- Predicates and combinators
--------------------------------------------------------------------------------

Predicate : Set -> Set
Predicate A = A -> Bool

-- Negation
¬_ : ∀ {a} -> Predicate a -> Predicate a
¬ p = λ a → not (p a)

-- Conjunction
_∧_ : ∀ {a} -> Predicate a -> Predicate a -> Predicate a
p ∧ q = λ a -> p a and q a

-- Direct interpretation
_∨_ : ∀ {a} -> Predicate a -> Predicate a -> Predicate a
p ∨ q = λ a -> (p a) or (q a) 

-- Implies
_⇒_ : ∀ {a} -> Predicate a -> Predicate a -> Predicate a
p ⇒ q = λ a -> (not (p a)) or (q a) 

-- Valid 
⊧_ : ∀ {a} -> Predicate a -> Set
⊧ P = ∀ {a} -> T (P a)

--------------------------------------------------------------------------------
-- Precondition and postcondition predicates
--------------------------------------------------------------------------------

data PArg : Set where
  pArg : ∀ {n} -> Heap n -> PArg

data QArg : Set where
  qArg : ∀ {ty} -> Value ty -> PArg -> QArg

PredicateP : Set
PredicateP = Predicate PArg

PredicateQ : Set
PredicateQ = Predicate QArg

-- Lifts predicateP to PredicateQ (the result value is simply ignored). 
liftPQ : PredicateP -> PredicateQ
liftPQ p (qArg v parg) = p parg 

-- Lifts a boolean expression to a predicate (for signatures)
lift : Term Boolean -> PredicateP
lift t (pArg H) with ⟦ t ⟧ H
lift t (pArg H) | D.< vtrue , heap > = true
lift t (pArg H) | D.< _ , heap > = false

-- Specific lifts on the value level (for proofs)
lift-true : ∀ {n m} {H1 : Heap n} {H2 : Heap m} {c : Term Boolean} ->
            BStep {H1 = H1} {H2 = H2} c vtrue -> T (lift c (pArg H1))
lift-true {H1 = H1} {c = c} bstp with ⟦ c ⟧ H1 | ⇓sound _ _ bstp
lift-true {n} {m} {H1} {H2} bstp | .(D.< vtrue , H2 >) | refl = tt

lift-false : ∀ {n m} {H1 : Heap n} {H2 : Heap m} {c : Term Boolean} -> 
             BStep {H1 = H1} {H2 = H2} c vfalse -> T (not (lift c (pArg H1))) 
lift-false {H1 = H1} {c = c} bstp with ⟦ c ⟧ H1 | ⇓sound _ _ bstp
lift-false {n} {m} {H1} {H2} bstp | .(D.< vfalse , H2 >) | refl = tt

-- Examples
isEmpty : PredicateP
isEmpty (pArg Nil) = true
isEmpty (pArg (Cons v x)) = false

-- The predicate that holds in any state
True : ∀ {a} -> Predicate a
True _ = true

-- The predicate that never holds in any state
False : ∀ {a} -> Predicate a
False _ = false

------------------------------------------------------------------------------
-- Logics theorem and lemmas
--------------------------------------------------------------------------------
 
split∨ : ∀ p q -> T (p or q) -> (T p × T q) ⊎ ( T p ⊎ T q)
split∨ true true tpq = inj₁ (tt , tt)
split∨ true false tpq = inj₂ (inj₁ tt)
split∨ false true tpq = inj₂ (inj₂ tt)
split∨ false false () 

split∧ : ∀ p q -> T (p and q) -> T p × T q
split∧ true true tp = tt , tt
split∧ true false ()
split∧ false true ()
split∧ false false ()

double¬ : ∀ p -> T (not (not p)) -> T p
double¬ true tp = tt
double¬ false ()

pack∧ : ∀ {p q} -> T p -> T q -> T (p and q)
pack∧ {true} {true} TP TQ = tt
pack∧ {true} {false} TP ()
pack∧ {false} {true} () TQ
pack∧ {false} {false} () ()

pack∨ : ∀ p q -> T p  ⊎ T q -> T (p or q)
pack∨ true true t = tt
pack∨ true false t = tt
pack∨ false true t = tt
pack∨ false false (inj₁ ())
pack∨ false false (inj₂ ())

mp : ∀ {A} {a : A} → (P Q : Predicate A) → ⊧ (P ⇒ Q) → T (P a) → T (Q a)
mp {_} {a} p q v TP with p a | q a | v {a}
mp p q v TP | true | true | va = tt
mp p q v TP | true | false | ()
mp p q v () | false | qa | va

-- I don't know whether there is something from the standard library for this.
absurd : ∀ {p} -> T p -> T (not p) -> ⊥
absurd {true} p₁ p₂ = p₂
absurd {false} p₁ p₂ = p₁

------------------------------------------------------------------------------
-- Hoare triples
--------------------------------------------------------------------------------

-- Definition.
-- Exploiting T only valid hoare triples can be constructed.
<_>_<_> : ∀ {ty} -> PredicateP -> Term ty -> PredicateQ -> Set
<_>_<_> {ty} P S Q = ∀ {n m} -> {H1 : Heap n} {H2 : Heap m} {v : Value ty} ->
                     BStep {H1 = H1} {H2 = H2} S v -> T (P (pArg H1)) -> T (Q (qArg v (pArg H2)))

-- Examples
trivial : ∀ {ty} {t : Term ty} -> < True > t < True >
trivial = λ {ty} {t} {n} {m} {H1} {H2} {v} _ _ → tt

-- An invalid hoare triple cannot be constructed
invalid : ∀ {ty n m} {H1 : Heap n} {H2 : Heap m} {t : Term ty} {v : Value ty} -> 
          BStep {H1 = H1} {H2 = H2} t v -> < True > t < False > -> ⊥ 
invalid bstp triple = triple bstp tt


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


data HeapEq : ∀ {n m} -> Heap n -> Heap m -> Set where
  Refl : ∀ {n} -> {H : Heap n} -> HeapEq H H


⇓expr-preserves-heap : ∀ {ty n m} {H1 : Heap n} {H2 : Heap m} {t : Term ty} {v : Value ty} -> (isExpr t) -> BStep {H1 = H1} {H2 = H2} t v -> HeapEq H1 H2
⇓expr-preserves-heap isEx E-True = Refl
⇓expr-preserves-heap isEx E-False = Refl
⇓expr-preserves-heap isEx E-Num = Refl
⇓expr-preserves-heap isEx E-Ref = Refl
⇓expr-preserves-heap isEx E-Error = Refl
⇓expr-preserves-heap isEx (E-IfTrue bstp bstp₁) with ⇓expr-preserves-heap (proj₁ isEx) bstp | ⇓expr-preserves-heap (proj₁ (proj₂ isEx)) bstp₁
⇓expr-preserves-heap {ty} {.m} {m} {.H2} {H2} (_ , _) (E-IfTrue bstp bstp₁) | Refl | Refl = Refl
⇓expr-preserves-heap isEx (E-IfFalse bstp bstp₁) with ⇓expr-preserves-heap (proj₁ isEx) bstp | ⇓expr-preserves-heap (proj₂ (proj₂ isEx)) bstp₁
⇓expr-preserves-heap {ty} {.m} {m} {.H2} {H2} (_ , _) (E-IfFalse bstp bstp₁) | Refl | Refl = Refl
⇓expr-preserves-heap isEx (E-IfErr bstp) = ⇓expr-preserves-heap (proj₁ isEx) bstp
⇓expr-preserves-heap isEx (E-IsZerZ bstp) = ⇓expr-preserves-heap isEx bstp
⇓expr-preserves-heap isEx (E-IsZerS bstp) = ⇓expr-preserves-heap isEx bstp
⇓expr-preserves-heap isEx (E-IsZerErr bstp) = ⇓expr-preserves-heap isEx bstp
⇓expr-preserves-heap () (E-New bstp)
⇓expr-preserves-heap () (E-NewErr bstp)
⇓expr-preserves-heap isEx (E-Deref bstp) = ⇓expr-preserves-heap isEx bstp
⇓expr-preserves-heap isEx (E-DerefErr bstp) = ⇓expr-preserves-heap isEx bstp
⇓expr-preserves-heap () (E-Ass bstp bstp₁)
⇓expr-preserves-heap () (E-AssErr bstp)
⇓expr-preserves-heap isEx (E-Seq x bstp bstp₁) with ⇓expr-preserves-heap (proj₁ isEx) bstp | ⇓expr-preserves-heap (proj₂ isEx) bstp₁
⇓expr-preserves-heap ty1 (E-Seq x bstp bstp₁) | Refl | Refl = Refl
⇓expr-preserves-heap isEx (E-SeqErr bstp) = ⇓expr-preserves-heap (proj₁ isEx) bstp

-- examples
const-exprs : isExpr (Base.true)
const-exprs = tt

if-expr : isExpr (if Base.false then (num 1) else error)
if-expr = tt , tt , tt

NotError  : ∀ {ty} (t : Term ty) -> Set
NotError t = ∀ {n m} {H1 : Heap n} {H2 : Heap m} -> BStep {H1 = H1} {H2 = H2} t verror -> ⊥

--------------------------------------------------------------------------------
-- Theorems
--------------------------------------------------------------------------------

-- If the post condition is valid (⊧ Q) then for any precondition P and any program S
-- the hoare triple < P > S < Q > holds.
postTrue : ∀ {ty} {v : Value ty} {P : PredicateP} {Q : PredicateQ} {S : Term ty} -> ⊧ Q -> < P > S < Q >
postTrue validQ bstp TP = validQ

-- If the precondition is always false in any state ( ⊧ (¬ P) ) then any program S and any post condition Q
-- form a valid hoare triple < P > S < Q > . The point is that Hoare triples have the premises that the precondition
-- holds. If this is not the case I do not have any obligation.
preFalse : ∀ {ty} {P : PredicateP} {Q : PredicateQ} {S : Term ty} ->  ⊧ (¬ P) -> < P > S < Q >
preFalse invalidP bstp P = ⊥-elim (absurd P invalidP)

-- Precondition strengthening (total interpretation)
preStrength : ∀ {ty} {P P' : PredicateP} {Q : PredicateQ} {S : Term ty} ->
              ⊧ (P ⇒ P') -> < P' > S < Q > -> < P > S < Q >
preStrength {P = P} {P' = P'} p2p' triple {n} {m} {H1} with split∨ (not (P (pArg H1))) (P' (pArg H1)) p2p'
preStrength p2p' triple | inj₁ (TP , TP') = λ bstp _ → triple bstp TP'
preStrength p2p' triple | inj₂ (inj₁ notTP) = λ bstp TP → ⊥-elim (absurd TP notTP)
preStrength p2p' triple | inj₂ (inj₂ TP') = λ bstp _ → triple bstp TP'

-- Postcondition weakening (total interpretation)
postWeak : ∀ {ty} {P : PredicateP} {Q Q' : PredicateQ} {S : Term ty} ->
           ⊧ (Q' ⇒ Q) -> < P > S < Q' > -> < P > S < Q >
postWeak {P = P} {Q = Q} {Q' = Q'} qq triple {n} {m} {H1} {H2} s TP with split∨ (not (Q' (qArg _ (pArg H2)))) (Q (qArg _ (pArg H2))) qq 
postWeak qq triple s TP | inj₁ (proj₁ , proj₂) = proj₂
postWeak qq triple s TP | inj₂ (inj₁ x) = ⊥-elim (absurd (triple s TP) x)
postWeak qq triple s TP | inj₂ (inj₂ y) = y

-- This is the usual theorem for if-then-else statement with total interpretation 
-- in which the condition is restricted to be an expression
hoare-if : ∀ {ty} {P : PredicateP} {R Q : PredicateQ} {c : Term Boolean} {S1 S2 : Term ty} {isEx : isExpr c} {notE : NotError c} ->
              < P ∧ lift c > S1 < Q > -> < P ∧ (¬ (lift c)) > S2 < Q > -> < P > if c then S1 else S2 < Q >
hoare-if {isEx = isEx}  pS1q pS2q (E-IfTrue bstp bstp₁) TP with ⇓expr-preserves-heap isEx bstp 
hoare-if {isEx = isEx} pS1q pS2q (E-IfTrue bstp bstp₁) TP | Refl = pS1q bstp₁ (pack∧ TP (lift-true bstp)) 
hoare-if {isEx = isEx} pS1q pS2q (E-IfFalse bstp bstp₁) TP with ⇓expr-preserves-heap isEx bstp
hoare-if {isEx = isEx} pS1q pS2q (E-IfFalse bstp bstp₁) TP | Refl = pS2q bstp₁ (pack∧ TP (lift-false bstp))
hoare-if {notE = notE} pS1q pS2q (E-IfErr bstp) TP = ⊥-elim (notE bstp)

-- hoare-if : ∀ {ty} {P : PredicateP} {R Q : PredicateQ} {c : Term Boolean} {S1 S2 : Term ty} →
--            (isEx : isExpr c) → < P ∧ lift c > S1 < Q > → < P ∧ (¬ (lift c)) > S2 < Q > → ⊧ (P ⇒ (λ x → Q (qArg {Boolean} verror x))) →
--            < P > if c then S1 else S2 < Q >
-- hoare-if {c = c} isEx t-t t-e err {H1 = H1} (E-IfTrue bstp bstp₁) TP with ⟦ c ⟧ H1 | ⇓sound _ _  bstp | ⇓expr-preserves-heap isEx bstp
-- hoare-if isEx t-t t-e err (E-IfTrue bstp bstp₁) TP | D.< vtrue , H2 > | refl | Refl = t-t bstp₁ (pack TP (lift-true {_} {_} {_} {_} {_} {isEx} bstp))
-- hoare-if {c = c} isEx t-t t-e err {H1 = H1} (E-IfFalse bstp bstp₁) TP with ⟦ c ⟧ H1 | ⇓sound _ _  bstp | ⇓expr-preserves-heap isEx bstp
-- hoare-if isEx t-t t-e err (E-IfFalse bstp bstp₁) TP | D.< vfalse , H2 > | refl | Refl = t-e bstp₁ (pack TP (lift-false bstp))
-- hoare-if {c = c} isEx t-t t-e err {H1 = H1} (E-IfErr bstp) TP with ⇓expr-preserves-heap isEx bstp
-- hoare-if {P = P} {Q = Q} isEx t-t t-e err {H1 = H1} {H2 = .H1} (E-IfErr bstp) TP | Refl with err {pArg H1}
-- ... | e with split (not (P (pArg H1))) (Q (qArg verror (pArg H1))) e
-- hoare-if isEx t-t t-e err (E-IfErr bstp) TP | Refl | e | inj₁ (proj₁ , proj₂) = {!!}
-- hoare-if isEx t-t t-e err (E-IfErr bstp) TP | Refl | e | inj₂ (inj₁ x) = ⊥-elim (lemma TP x)
-- hoare-if isEx t-t t-e err (E-IfErr bstp) TP | Refl | e | inj₂ (inj₂ y) = {!!}
--hoare-if {c = c} t-c t-t t-e {H1 = H1} (E-IfTrue bstp bstp₁) TP with ⟦ c ⟧ H1 | ⇓sound _ _  bstp
-- T      (.R (qArg vtrue (pArg H2)) and (lift .c (pArg H2) | ⟦ .c ⟧ H2))
-- hoare-if t-c t-t t-e {H1 = H1} (E-IfTrue bstp bstp₁) TP | (D.< vtrue , H2 >) | refl = t-t bstp₁ (pack (t-c bstp TP) (lift-true {!!}))
-- hoare-if t-c t-t t-e (E-IfFalse bstp bstp₁) TP = {!!}
-- hoare-if t-c t-t t-e (E-IfErr bstp) TP = {!!}
--... | ec | ss = {!!}

getPArg : QArg -> PArg
getPArg (qArg x x₁) = x₁

withError : {ty : Type} -> QArg -> QArg
withError {ty} (qArg x x₁) = qArg {ty} verror x₁


-- Sequence rule for hoare triples
hoare-seq2 : ∀ {ty ty'} {P R' : PredicateP} {R Q : PredicateQ} {S1 : Term ty} {S2 : Term ty'} →
            < P > S1 < R > → < R' > S2 < Q > → ⊧ (R ⇒ (λ x → R' (getPArg x))) → ⊧ (λ x → ((λ y → R (withError {ty} x)) ⇒ (λ y → Q (withError {ty'} x))) x) →  --((λ x → R (withError {ty} x)) ⇒ (λ x → Q (withError {ty'} x))) →
            < P > S1 >> S2 < Q >
hoare-seq2 {_} {_} {_} {R'} {R} pS1r rS2q seq err (E-Seq x bstp bstp₁) TP with pS1r bstp TP
... | s1 with mp R (λ z → R' (getPArg z)) seq s1
... | i = rS2q bstp₁ i
hoare-seq2 {ty} {ty'} {R = R} {Q = Q} pS1r rS2q seq err (E-SeqErr {H2 = H2} bstp) TP with pS1r bstp TP
... | s1 with err {qArg vtrue (pArg H2)}
... | err' with mp {_} {verror} (λ x → R (withError (qArg {ty} x (pArg H2)))) (λ x → Q (qArg verror (pArg H2))) err' s1
... | i = i


-- Sequence rule with total interpretation.
hoare-seq-no-error : ∀ {ty ty'} {P Q : PredicateP} {R : PredicateQ} {S1 : Term ty} {S2 : Term ty'} (notE : NotError S1) ->
                       < P > S1 < liftPQ Q > -> < Q > S2 < R > -> < P > S1 >> S2 < R >
hoare-seq-no-error notE pS1q qS2r (E-Seq x bstp bstp₁) TP = qS2r bstp₁ (pS1q bstp TP)
hoare-seq-no-error notE pS1q qS2r (E-SeqErr bstp) TP = ⊥-elim (notE bstp)

-- It's true when the result of the last computation is verror
fail : PredicateQ
fail (qArg vtrue pa) = false
fail (qArg vfalse pa) = false
fail (qArg (vnat x) pa) = false
fail (qArg (vref x) pa) = false
fail (qArg verror pa) = true

-- If we have failed the resulting value is a verror.
fail2error : ∀ {ty n} {H : Heap n} {v : Value ty} -> T (fail (qArg v (pArg H))) -> isVError v 
fail2error {.Boolean} {n} {H} {vtrue} ()
fail2error {.Boolean} {n} {H} {vfalse} ()
fail2error {.Natural} {n} {H} {vnat x} ()
fail2error {.(Ref _)} {n} {H} {vref x} ()
fail2error {ty} {n} {H} {verror} TF = unit 

-- Hoare sequencing with partial interpretation
hoare-seq : ∀ {ty ty'} {P Q : PredicateP} {R : PredicateQ} {S1 : Term ty} {S2 : Term ty'} ->
              < P > S1 < (¬ fail) ⇒ liftPQ Q > -> < Q > S2 < R > -> < P > S1 >> S2 < (¬ fail) ⇒ R >
hoare-seq ps1q qs2r (E-Seq {H1 = H1} {H2 = H2} {v1 = v1} {v2 = v2} x bstp bstp₁) TP with split∨ (not (not (fail (qArg v1 (pArg _))))) _ (ps1q bstp TP)
hoare-seq ps1q qs2r (E-Seq {H1 = H1} {H2 = H2} {v1 = v1} {v2 = v2} x₁ bstp bstp₁) TP | inj₁ (proj₁ , proj₂) = pack∨ (not (not (fail (qArg v2 (pArg _))))) _ (inj₂ (qs2r bstp₁ proj₂))
hoare-seq ps1q qs2r (E-Seq notE bstp bstp₁) TP | inj₂ (inj₁ x) = ⊥-elim (notE (fail2error (double¬ _ x)))
hoare-seq ps1q qs2r (E-Seq {H1 = H1} {H2 = H2} {v1 = v1} {v2 = v2} x bstp bstp₁) TP | inj₂ (inj₂ y) = pack∨ (not (not (fail (qArg v2 (pArg _))))) _ (inj₂ (qs2r bstp₁ y))
hoare-seq ps1q qs2r (E-SeqErr bstp) TP = tt
