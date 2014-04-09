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

try-replace : ∀ {ty n} {H : Heap n} -> ℕ -> Value ty -> ((Heap n) × (Value ty))
try-replace {ty} {n} {H} i v with elem? H i ty
try-replace {_} {_} {H} i v | inj₁ x = replace H x v , v
try-replace {_} {_} {H} i v | inj₂ y = H , verror

replace-result : ∀ {n H fn ty} -> Value ty -> ((Elem {n} H fn ty) ⊎ (¬ (Elem {n} H fn ty))) -> Value ty
replace-result v (inj₁ x) = v
replace-result v (inj₂ y) = verror

replace-heap : ∀ {n H fn ty} -> Value ty -> ((Elem {n} H fn ty) ⊎ (¬ (Elem {n} H fn ty))) -> Heap n
replace-heap {_} {H} v (inj₁ x) = replace H x v
replace-heap {_} {H} v (inj₂ y) = H


-- TODO: there should be no isValue proofs in the big steps. Instead take another bigstep as parameter which reduces the argment to a value. (e.g. E-New)
-- TODO sequencing ( I think try-catch is also missing)

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
  E-IsZerZ   : ∀ {  n1 n2} {H1 : Heap n1} {H2 : Heap n2} {t : Term Natural} →
               BStep {H1 = H1} {H2 = H2} t          (vnat 0)                →
               BStep {H1 = H1} {H2 = H2} (iszero t) vtrue

  E-IsZerS   : ∀ {n1 n2} {H1 : Heap n1} {H2 : Heap n2} {t : Term Natural} {n : ℕ} →
               BStep {H1 = H1} {H2 = H2} t          (vnat (suc n))          →
               BStep {H1 = H1} {H2 = H2} (iszero t) vfalse

  E-IsZerErr : ∀ {  n1 n2} {H1 : Heap n1} {H2 : Heap n2} {t : Term Natural} →
               BStep {H1 = H1} {H2 = H2} t          verror                  →
               BStep {H1 = H1} {H2 = H2} (iszero t) verror

-- refs
  E-New      : ∀ {ty n m} {H1 : Heap n} {H2 : Heap m} {t : Term ty} {v : Value ty} →
               BStep {H1 = H1} {H2 = H2}        t            v                     →
               BStep {H1 = H1} {H2 = Cons v H2} (new t)      (vref 0)

  E-NewErr   : ∀ {ty n m} {H1 : Heap n} {H2 : Heap m}  {t : Term ty}               →
               BStep {H1 = H1} {H2 = H2}        t            verror                →
               BStep {H1 = H1} {H2 = H2}        (new t)      verror

  E-Deref    : ∀ {ty n m r} {H1 : Heap n} {H2 : Heap m} {t : Term (Ref ty)}        →
               BStep {H1 = H1} {H2 = H2}        t            (vref r)              →
               BStep {H1 = H1} {H2 = H2}        (! t)        (lookup r H2)

  E-DerefErr : ∀ {ty n m  } {H1 : Heap n} {H2 : Heap m} {t : Term (Ref ty)}        →
               BStep {H1 = H1} {H2 = H2}        t            verror                →
               BStep {H1 = H1} {H2 = H2}        (! t)        verror

  E-Ass      : ∀ {ty n m k r} {H1 : Heap n} {H2 : Heap m} {H3 : Heap k}
               {t1 : Term (Ref ty)} {t2 : Term ty} {v2 : Value ty}                 →
               BStep {H1 = H1} {H2 = H2}        t1            (vref r)             →
               BStep {H1 = H2} {H2 = H3}        t2            v2                   →
               let e = elem? H3 r ty in
               BStep {ty} {n} {k} {H1 = H1} {H2 = replace-heap v2 e }
                                                (ref r <- t2) (replace-result v2 e)

  E-AssErr   : ∀ {ty n m} {H1 : Heap n} {H2 : Heap m} {t : Term ty} {v : Value ty} →
               BStep {H1 = H1} {H2 = H2}        t            verror                →
               BStep {H1 = H1} {H2 = H2}
                                                (ref m <- t) verror

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


--------------------------------------------------------------------------------
-- Conversion between BigStep and SmallStep
--------------------------------------------------------------------------------

-- An extension of the E-If rule, for multiple steps.
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

E-Ass* : ∀ {ty n m r} {H1 : Heap n} {H2 : Heap m} {t t' : Term ty} ->
         Steps {H1 = H1} {H2 = H2} t t' -> 
         Steps {H1 = H1} {H2 = H2} (ref r <- t) (ref r <- t') 
E-Ass* [] = []
E-Ass* (x :: stps) = E-AssRight (unit , (λ x₁ → x₁)) x :: E-Ass* stps

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


-- Lemmas used for small-to-big
-- Converstion from big- to small-step representations.
{-
big-to-small : forall {ty n m} {H1 : Heap n} {H2 : Heap m} {t : Term ty} {v : Value ty} ->
               BStep {H1 = H1} {H2 = H2} t v -> Steps {H1 = H1} {H2 = H2} t ⌜ v ⌝
big-to-small E-True  = []
big-to-small E-False = []
big-to-small E-Num   = []
big-to-small E-Ref   = []
big-to-small E-Error = []

big-to-small (E-IfTrue  bstp1 bstp2) = E-If* (big-to-small bstp1) ++ (E-IfTrue  :: big-to-small bstp2)
big-to-small (E-IfFalse bstp1 bstp2) = E-If* (big-to-small bstp1) ++ (E-IfFalse :: big-to-small bstp2)
big-to-small (E-IfErr   bstp       ) = E-If* (big-to-small bstp) ++ [ E-If-Err ]

big-to-small (E-IsZerZ   bstp) = E-IsZero* (big-to-small bstp) ++ [ E-IsZeroZero ]
big-to-small (E-IsZerS   bstp) = E-IsZero* (big-to-small bstp) ++ [ E-IsZeroSucc ]
big-to-small (E-IsZerErr bstp) = E-IsZero* (big-to-small bstp) ++ [ E-IsZero-Err ]

big-to-small (E-New      bstp) = E-New*   (big-to-small bstp) ++ [ E-NewVal refl ]
big-to-small (E-NewErr   bstp) = E-New*   (big-to-small bstp) ++ [ {!!}          ]
big-to-small (E-Deref    bstp) = E-Deref* (big-to-small bstp) ++ [ E-DerefVal    ]
big-to-small (E-DerefErr bstp) = E-Deref* (big-to-small bstp) ++ [ E-Deref-Err   ]
big-to-small (E-Ass      bstp) = E-Ass*   (big-to-small bstp) ++ [ {!!}          ]
big-to-small (E-AssErr   bstp) = E-Ass*   (big-to-small bstp) ++ [ {!!}          ]

big-to-small (E-Seq    bstp1 bstp2 bstp3) = {!!}
big-to-small (E-SeqErr bstp             ) = {!!}
-}

-- A value term evaluates to itself.

value-of-value : forall {ty n} {H : Heap n} -> (v : Value ty) -> BStep {H1 = H} {H2 = H} ⌜ v ⌝ v
value-of-value vtrue = E-True
value-of-value vfalse = E-False
value-of-value (vnat n) = E-Num
value-of-value (vref x) = E-Ref
value-of-value verror = E-Error

-- Combining a single small step with a big step.

{-prepend-step : forall {ty n1 n2 n3} {H1 : Heap n1} {H2 : Heap n2} {H3 : Heap n3} {t1 t2 : Term ty} {v : Value ty} -> 
               Step {H1 = H1} {H2 = H2} t1 t2 -> BStep {H1 = H2} {H2 = H3} t2 v -> BStep {H1 = H1} {H2 = H3} t1 v
prepend-step E-IsZeroZero E-True         = E-IsZerZ   E-Num
prepend-step E-IsZeroSucc E-False        = E-IsZerS   E-Num
prepend-step (E-IsZero s) (E-IsZerZ b  ) = E-IsZerZ   (prepend-step s b)
prepend-step (E-IsZero s) (E-IsZerS b  ) = E-IsZerS   (prepend-step s b)
prepend-step (E-IsZero s) (E-IsZerErr b) = E-IsZerErr (prepend-step s b)
prepend-step E-IsZero-Err E-Error        = E-IsZerErr E-Error

prepend-step E-IfTrue  b = E-IfTrue  E-True  b
prepend-step E-IfFalse b = E-IfFalse E-False b

prepend-step (E-If s) (E-IfTrue  b1 b2) = E-IfTrue  (prepend-step s b1) b2
prepend-step (E-If s) (E-IfFalse b1 b2) = E-IfFalse (prepend-step s b1) b2
prepend-step (E-If s) (E-IfErr   b    ) = E-IfErr   (prepend-step s b )
prepend-step E-If-Err E-Error           = E-IfErr E-Error

prepend-step (E-New s) (E-New    b) = E-New    (prepend-step s b)
prepend-step (E-New s) (E-NewErr b) = E-NewErr (prepend-step s b)
prepend-step (E-NewVal refl) E-Ref = E-New (value-of-value _)

prepend-step (E-Deref s) (E-Deref    b) = E-Deref    (prepend-step s b)
prepend-step (E-Deref s) (E-DerefErr b) = E-DerefErr (prepend-step s b)
prepend-step E-DerefVal  b              = {!!}
prepend-step E-Deref-Err E-Error        = E-DerefErr E-Error


prepend-step (E-AssLeft         s     ) b       = {!!}
prepend-step (E-AssRight    isV s     ) b       = {!!}
prepend-step (E-AssRed-Suc {ty} {n} {r} {H1} {H2} {t} {v} isV eq rep) b    with elem? H1 r ty
... | inj₁ x with replace-heap v (inj₁ rep) | replace-result v (inj₁ rep)
... | rh | rr rewrite (sym eq) = E-Ass {ty} {n} {n} {{!!}} {r} {H1} {H1} {{!!}} {ref r} E-Ref {!!}
--... | rh rewrite (sym eq) with value-of-value {ty} {n} {H1} v
--... | vov = E-Ass {ty} {n} {n} {_} {r} {H1} {H1} {{!!}} {ref r} E-Ref {!!}
-- E-Ass {ty} {n} {n} {{!!}} {r} {H1} {H1} {replace-heap v (inj₁ {!!})} {ref r} {t} {v} E-Ref {!!}
-- ... | inj₁ x with replace-result {n} {H1} v (inj₁ x)
-- --... | rr = {!E-A!}
-- ... | rr  with replace-heap v (inj₁ rep)
-- --Goal: BStep (ref .r <- .t2) .v
-- ... | rh rewrite (sym eq) = E-Ass E-Ref {!!}
prepend-step (E-AssRed-Suc {v = v} isV eq rep) b | inj₂ y = ⊥-elim (y rep)
prepend-step (E-AssRed-Fail notRep    ) E-Error = {!!}
prepend-step E-Assign-Err1              E-Error = {!!}

prepend-step (E-Seq1   s) b       = {!!}
prepend-step (E-SeqVal x) b       = {!!}
prepend-step E-Seq-Err    E-Error = E-SeqErr E-Error

prepend-step (E-Try-Catch      s  ) b = {!!}
prepend-step (E-Try-Catch-Suc  x  ) b = {!!}
prepend-step (E-Try-Catch-Fail isE) b = {!!}


small-to-big : ∀ {ty n m} {H1 : Heap n} {H2 : Heap m} {t : Term ty} {v : Value ty} → 
               Steps {H1 = H1} {H2 = H2} t ⌜ v ⌝ -> BStep {H1 = H1} {H2 = H2} t v
small-to-big [] = value-of-value _
small-to-big (stp :: stps) = prepend-step stp (small-to-big stps)

-}
