module BigStep where

open import Data.Nat
open import Data.Product
open import Data.Unit
open import Data.Sum
open import Data.Empty
open import Relation.Nullary
open import Base
open import SmallStep

open import Relation.Binary.PropositionalEquality hiding ( [_] ) -- remove


data BStep : ∀ {ty n m} {H1 : Heap n} {H2 : Heap m} -> Term ty → Value ty → Set where

-- values
  E-True     : ∀ {n} {H : Heap n} →
               BStep {H1 = H} {H2 = H}          true    vtrue

  E-False    : ∀ {n} {H : Heap n} →
               BStep {H1 = H} {H2 = H}          false   vfalse

  E-Num      : ∀ {n m} {H : Heap n} →
               BStep {H1 = H} {H2 = H}          (num m) (vnat m)

  E-Ref      : ∀ {n m ty} {H : Heap n} →
               BStep {Ref ty} {H1 = H} {H2 = H} (ref m) (vref m)

  E-Error    : ∀ {ty n} {H : Heap n} →
               BStep {ty} {H1 = H} {H2 = H}     error   verror

-- if
  E-IfTrue   : ∀ {ty} {n1 n2 n3} {H1 : Heap n1} {H2 : Heap n2} {H3 : Heap n3} 
                 {t : Term Boolean} {t1 t2 : Term ty} {v : Value ty}  →
               BStep {H1 = H1} {H2 = H2} t                      vtrue →
               BStep {H1 = H2} {H2 = H3} t1                     v     →
               BStep {H1 = H1} {H2 = H3} (if t then t1 else t2) v

  E-IfFalse  : ∀ {ty} {n1 n2 n3} {H1 : Heap n1} {H2 : Heap n2} {H3 : Heap n3} 
                 {t : Term Boolean} {t1 t2 : Term ty} {v : Value ty}   →
               BStep {H1 = H1} {H2 = H2} t                      vfalse →
               BStep {H1 = H2} {H2 = H3} t2                     v      →
               BStep {H1 = H1} {H2 = H3} (if t then t1 else t2) v

  E-IfErr    : ∀ {ty} {n1 n2} {H1 : Heap n1} {H2 : Heap n2}
                 {t : Term Boolean} {t1 t2 : Term ty} →
               BStep {H1 = H1} {H2 = H2} t                      verror →
               BStep {H1 = H1} {H2 = H2} (if t then t1 else t2) verror

-- isZero
  E-IsZerZ   : ∀ {  n1 n2} {H1 : Heap n1} {H2 : Heap n2} {t : Term Natural}       →
               BStep {H1 = H1} {H2 = H2} t          (vnat 0)                      →
               BStep {H1 = H1} {H2 = H2} (iszero t) vtrue

  E-IsZerS   : ∀ {n1 n2} {H1 : Heap n1} {H2 : Heap n2} {t : Term Natural} {n : ℕ} →
               BStep {H1 = H1} {H2 = H2} t          (vnat (suc n))                →
               BStep {H1 = H1} {H2 = H2} (iszero t) vfalse

  E-IsZerErr : ∀ {  n1 n2} {H1 : Heap n1} {H2 : Heap n2} {t : Term Natural}       →
               BStep {H1 = H1} {H2 = H2} t          verror                        →
               BStep {H1 = H1} {H2 = H2} (iszero t) verror

-- refs
  E-New      : ∀ {ty n m} {H1 : Heap n} {H2 : Heap m} {t : Term ty} {v : Value ty}        →
               BStep {H1 = H1} {H2 = H2}        t             v                           →
               BStep {H1 = H1} {H2 = append H2 v} (new t)     (vref m)

  E-Deref    : ∀ {ty n m r} {H1 : Heap n} {H2 : Heap m} {t : Term (Ref ty)}               →
               BStep {H1 = H1} {H2 = H2}        t             (vref r)                    →
               BStep {H1 = H1} {H2 = H2}        (! t)         (lookup r H2)

  E-DerefErr : ∀ {ty n m  } {H1 : Heap n} {H2 : Heap m} {t : Term (Ref ty)}               →
               BStep {H1 = H1} {H2 = H2}        t             verror                      →
               BStep {H1 = H1} {H2 = H2}        (! t)         verror

  E-Ass      : ∀ {ty n1 n2 n3 r} {H1 : Heap n1} {H2 : Heap n2} {H3 : Heap n3}
               {t1 : Term (Ref ty)} {t2 : Term ty} {v : Value ty}                         →
               (rep : Elem H3 r ty)                                                       →
               BStep {H1 = H1} {H2 = H2}        t1            (vref r)                    →
               BStep {H1 = H2} {H2 = H3}        t2            v                           →
               BStep {H1 = H1} {H2 = replace H3 rep v }
                                                (t1 <- t2)    v

  E-AssOob   : ∀ {ty n1 n2 n3 r} {H1 : Heap n1} {H2 : Heap n2} {H3 : Heap n3}
               {t1 : Term (Ref ty)} {t2 : Term ty} {v : Value ty}                         →
               ¬ (Elem H3 r ty)                                                           →
               BStep {H1 = H1} {H2 = H2}        t1            (vref r)                    →
               BStep {H1 = H2} {H2 = H3}        t2            v                           →
               BStep {H1 = H1} {H2 = H3}        (t1 <- t2)    verror

  E-AssErr   : ∀ {ty n m} {H1 : Heap n} {H2 : Heap m}
                 {t1 : Term (Ref ty)} {t2 : Term ty}                                      →
               BStep {H1 = H1} {H2 = H2}        t1            verror                      →
               BStep {H1 = H1} {H2 = H2}        (t1 <- t2)    verror

-- seq
  E-Seq      : ∀ {ty1 ty2 n1 n2 n3} {H1 : Heap n1} {H2 : Heap n2} {H3 : Heap n3}
                 {t1 : Term ty1} {v1 : Value ty1} {t2 : Term ty2} {v2 : Value ty2} →
               ¬ (isVError v1) →
               BStep {H1 = H1} {H2 = H2} t1         v1                             →
               BStep {H1 = H2} {H2 = H3} t2         v2                             →
               BStep {H1 = H1} {H2 = H3} (t1 >> t2) v2

  E-SeqErr   : ∀ {ty1 ty2 n1 n2} {H1 : Heap n1} {H2 : Heap n2}
                 {t1 : Term ty1} {t2 : Term ty2}                                   → 
               BStep {H1 = H1} {H2 = H2} t1         verror                         →
               BStep {H1 = H1} {H2 = H2} (t1 >> t2) verror

-- try-catch
  E-TryCat   : ∀ {ty n1 n2} {H1 : Heap n1} {H2 : Heap n2}
                 {t1 : Term ty} {t2 : Term ty} {v : Value ty}               →
               ¬ (isVError v)                                               →
               BStep {H1 = H1} {H2 = H2} t1                v                →
               BStep {H1 = H1} {H2 = H2} (try t1 catch t2) v

  E-TryCatEx : ∀ {ty n1 n2 n3} {H1 : Heap n1} {H2 : Heap n2} {H3 : Heap n3}
                 {t1 : Term ty} {t2 : Term ty} {v : Value ty}               →
               BStep {H1 = H1} {H2 = H2} t1                verror           →
               BStep {H1 = H2} {H2 = H3} t2                v                →
               BStep {H1 = H1} {H2 = H3} (try t1 catch t2) v


--------------------------------------------------------------------------------
-- Star extensions
--------------------------------------------------------------------------------

E-If* : ∀ {ty n m} {H1 : Heap n} {H2 : Heap m} {t₁ t₁′ : Term Boolean} {t₂ t₃ : Term ty} →
        Steps {H1 = H1} {H2 = H2} t₁ t₁′ →
        Steps {H1 = H1} {H2 = H2} (if t₁ then t₂ else t₃) (if t₁′ then t₂ else t₃)
E-If* [] = []
E-If* (x :: stps) = E-If x :: E-If* stps

E-New* : ∀ {ty n m} {H1 : Heap n} {H2 : Heap m} {t t′ : Term ty} ->
        Steps {H1 = H1} {H2 = H2} t t′ →
        Steps {H1 = H1} {H2 = H2} (new t) (new t′)
E-New* [] = []
E-New* (x :: stps) = E-New x :: E-New* stps

E-AssR* : ∀ {ty n m r} {H1 : Heap n} {H2 : Heap m} {t t' : Term ty} ->
         Steps {H1 = H1} {H2 = H2} t t' -> 
         Steps {H1 = H1} {H2 = H2} (ref r <- t) (ref r <- t') 
E-AssR* [] = []
E-AssR* (x :: stps) = E-AssRight (unit , (λ x₁ → x₁)) x :: E-AssR* stps

E-AssL* : ∀ {ty n m} {H1 : Heap n} {H2 : Heap m} {t t' : Term (Ref ty)} {t2 : Term ty} ->
         Steps {H1 = H1} {H2 = H2} t t' -> 
         Steps {H1 = H1} {H2 = H2} (t <- t2) (t' <- t2) 
E-AssL* [] = []
E-AssL* (x :: xs) = E-AssLeft x :: E-AssL* xs

E-IsZero* : ∀ {t t' n m} {H1 : Heap n} {H2 : Heap m} ->
            Steps {H1 = H1} {H2 = H2} t t' ->
            Steps {H1 = H1} {H2 = H2} (iszero t) (iszero t')
E-IsZero* [] = []
E-IsZero* (x :: stps) = E-IsZero x :: E-IsZero* stps

E-Try* : ∀ {ty n m} {H1 : Heap n} {H2 : Heap m} {t t' t2 : Term ty} ->
            Steps {H1 = H1} {H2 = H2} t t' ->
            Steps {H1 = H1} {H2 = H2} (try t catch t2 ) (try t' catch t2)
E-Try* [] = []
E-Try* (x :: stps) = E-Try-Catch x :: E-Try* stps

E-Deref* : ∀ {ty n m} {H1 : Heap n} {H2 : Heap m} {t t' : Term (Ref ty)} ->
            Steps {H1 = H1} {H2 = H2} t t' ->
            Steps {H1 = H1} {H2 = H2} (! t) (! t')
E-Deref* [] = []
E-Deref* (x :: stps) = E-Deref x :: E-Deref* stps

E-Seq* : ∀ {ty1 ty2 n m} {H1 : Heap n} {H2 : Heap m} {t t' : Term ty1} {t2 : Term ty2} ->
            Steps {H1 = H1} {H2 = H2} t t' ->
            Steps {H1 = H1} {H2 = H2} (t >> t2) (t' >> t2)
E-Seq* [] = []
E-Seq* (x :: stps) = E-Seq1 x :: E-Seq* stps

