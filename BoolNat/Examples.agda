module Examples where

open import Data.Unit
open import Data.Empty
open import Data.Sum
open import Data.Nat
open import Data.Product
open import Data.Bool hiding ( if_then_else_ ) renaming ( _∧_ to _and_  ; _∨_ to _or_ )

open import Denotational as D
open import Base
open import BigStep
open import Hoare

-- Expression
const-exprs : isExpr (Base.true)
const-exprs = tt

if-expr : isExpr (if Base.false then (num 1) else error)
if-expr = tt , tt , tt

-- Denotational Semantics

-- Here the implicit type parameter fixes the type assigned to error
-- and determines which replace will fail. In both cases the failure is
-- due to the fact that type in the heap would not be preserved.
t : Term Natural
t = new true >> (_>>_ {Natural} (ref 0 <- error) (ref 0 <- num 1))

v : Result Natural
v = ⟦ t ⟧ Nil

-- Hoare

trivial : ∀ {ty} {t : Term ty} -> < True > t < True >
trivial = λ {ty} {t} {n} {m} {H1} {H2} {v} _ _ → tt

-- An invalid hoare triple cannot be constructed
invalid : ∀ {ty n m} {H1 : Heap n} {H2 : Heap m} {t : Term ty} {v : Value ty} -> 
          BStep {H1 = H1} {H2 = H2} t v -> < True > t < False > -> ⊥ 
invalid bstp triple = triple bstp tt

-- Short hands
_[_] : ∀ {ty n} -> Heap n -> ℕ -> Value ty
_[_] H n = lookup n H 

_==_ : ∀ {ty} -> Value ty -> Value ty -> Bool 
_==_ vtrue vtrue = true
_==_ vfalse vfalse = true
_==_ (vnat n) (vnat m) with compare n m
vnat .m == vnat m | equal .m = true
(vnat n) == (vnat m) | _ = false
_==_ (vref n) (vref m) with compare n m 
vref .m == vref m | equal .m = true
(vref m) == (vref n) | _ = false
_==_ verror verror = true
_==_ _ _ = false

p1 : Term (Ref Natural)
p1 = new (num 1)

Q1 : PredicateQ 
Q1 (qArg v (pArg H)) = (H [ 0 ] ) == vnat 1

-- It's very hard to use the hoare rules 
--h1 : < isEmpty > p1 < Q1 >
--h1 (E-New b) = {!!}
--h1 {.0} {.(suc _)} {Nil} {H2 = (append H2 v)} (E-New bstp) tt = {!!}

--  with ⟦ p1 ⟧ Nil | ⇓sound _ _ (E-New bstp) | ⟦ num 1 ⟧ Nil | ⇓sound _ _ bstp
-- h1 {._} {.(suc _)} {Nil} {Cons v H2} (E-New bstp) tt | .(D.< vref 0 , Cons v H2 >) | refl | .(D.< v , H2 >) | refl = {!!}

-- hoare-new {P = isEmpty} {Q = Q1} (pack∨ (not (isEmpty (pArg Nil))) (alloc (num 1) Q1 {!pArg ?!}) (inj₂ {!!})) (E-New bstp) tt
--  (pack∨ (not (isEmpty (pArg Nil))) (alloc (num 1) Q1 (pArg Nil)) (inj₂ tt)) (E-New bstp) {!!} -- 
--h1 {.(suc _)} {.(suc _)} {Cons v H1} (E-New bstp) ()

p2 : Term Boolean
p2 = if Base.true then Base.true else Base.false

Q2 : PredicateQ
Q2 (qArg vtrue x₁) = true
Q2 (qArg v x₁) = false

h2 : < True > p2 < Q2 >
h2 (E-IfTrue {v = vtrue} E-True bstp₁) tt = tt
h2 (E-IfTrue {v = vfalse} E-True ()) tt
h2 (E-IfTrue {v = verror} E-True ()) tt
h2 (E-IfFalse () bstp₁) tt
h2 (E-IfErr ()) tt
