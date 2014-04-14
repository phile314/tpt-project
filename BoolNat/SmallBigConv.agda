module SmallBigConv where

open import Data.Nat
open import Data.Product
open import Data.Unit
open import Data.Sum
open import Data.Empty
open import Relation.Nullary
open import Base
open import SmallStep
open import BigStep

open import Relation.Binary.PropositionalEquality hiding ( [_] ) -- remove

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


-- Lemmas used for small-to-big
-- Converstion from big- to small-step representations.

err-is-verr : ∀ {ty} {v : Value ty} -> isError ⌜ v ⌝ -> isVError v
err-is-verr {.Boolean} {vtrue} ()
err-is-verr {.Boolean} {vfalse} ()
err-is-verr {.Natural} {vnat x} ()
err-is-verr {Ref ty} {vref x} ()
err-is-verr {ty} {verror} err = unit


verr-is-err : ∀ {ty} {v : Value ty} -> isVError v -> isError ⌜ v ⌝
verr-is-err {.Boolean} {vtrue} ()
verr-is-err {.Boolean} {vfalse} ()
verr-is-err {.Natural} {vnat x} ()
verr-is-err {Ref ty} {vref x} ()
verr-is-err {ty} {verror} unit = unit

big-to-small : forall {ty n m} {H1 : Heap n} {H2 : Heap m} {t : Term ty} {v : Value ty} ->
               BStep {H1 = H1} {H2 = H2} t v -> Steps {H1 = H1} {H2 = H2} t ⌜ v ⌝
big-to-small E-True  = []
big-to-small E-False = []
big-to-small E-Num   = []
big-to-small E-Ref   = []
big-to-small E-Error = []

big-to-small (E-IfTrue  bstp1 bstp2) = E-If* (big-to-small bstp1) ++ (E-IfTrue  :: big-to-small bstp2)
big-to-small (E-IfFalse bstp1 bstp2) = E-If* (big-to-small bstp1) ++ (E-IfFalse :: big-to-small bstp2)
big-to-small (E-IfErr   bstp       ) = E-If* (big-to-small bstp ) ++ [ E-If-Err ]

big-to-small (E-IsZerZ   bstp) = E-IsZero* (big-to-small bstp) ++ [ E-IsZeroZero ]
big-to-small (E-IsZerS   bstp) = E-IsZero* (big-to-small bstp) ++ [ E-IsZeroSucc ]
big-to-small (E-IsZerErr bstp) = E-IsZero* (big-to-small bstp) ++ [ E-IsZero-Err ]

big-to-small (E-New      bstp) = E-New*   (big-to-small bstp) ++ [ E-NewVal refl ]

big-to-small (E-Deref    bstp) = E-Deref* (big-to-small bstp) ++ [ E-DerefVal    ]
big-to-small (E-DerefErr bstp) = E-Deref* (big-to-small bstp) ++ [ E-Deref-Err   ]

big-to-small (E-Ass    {v = v} rep  bstp1 bstp2) = (E-AssL* (big-to-small bstp1)) ++ ((E-AssR* (big-to-small bstp2)) ++ [ (E-AssRed-Suc (isValue? v) refl rep) ])
big-to-small (E-AssOob {v = v} nrp  bstp1 bstp2) = (E-AssL* (big-to-small bstp1)) ++ (E-AssR* (big-to-small bstp2) ++ [ (E-AssRed-Fail {isV = (isValue? v)} nrp) ])
big-to-small (E-AssErr        bstp       ) = (E-AssL* (big-to-small bstp)) ++ [ E-Assign-Err1 ]

big-to-small (E-Seq {v1 = v1} nEr bstp bstp2 ) = (E-Seq* (big-to-small bstp)) ++ ((E-SeqVal ((isValue? v1) , (λ x → nEr (err-is-verr x)))) :: big-to-small bstp2)
big-to-small (E-SeqErr bstp             ) = (E-Seq* (big-to-small bstp)) ++ [ E-Seq-Err ]

big-to-small {v = v} (E-TryCat   ner b    ) = E-Try* (big-to-small b) ++ [ E-Try-Catch-Suc ((isValue? v) , (λ x → ner (err-is-verr x))) ]
big-to-small (E-TryCatEx b1 b2) = (E-Try* (big-to-small b1)) ++ ((E-Try-Catch-Fail unit) :: big-to-small b2)


-- A value term evaluates to itself.

value-of-value : forall {ty n} {H : Heap n} -> (v : Value ty) -> BStep {H1 = H} {H2 = H} ⌜ v ⌝ v
value-of-value vtrue = E-True
value-of-value vfalse = E-False
value-of-value (vnat n) = E-Num
value-of-value (vref x) = E-Ref
value-of-value verror = E-Error

-- Combining a single small step with a big step.

prepend-step : forall {ty n1 n2 n3} {H1 : Heap n1} {H2 : Heap n2} {H3 : Heap n3} {t1 t2 : Term ty} {v : Value ty} -> 
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
prepend-step (E-NewVal refl) E-Ref = E-New (value-of-value _)

prepend-step (E-Deref s) (E-Deref    b) = E-Deref    (prepend-step s b)
prepend-step (E-Deref s) (E-DerefErr b) = E-DerefErr (prepend-step s b)
prepend-step E-DerefVal  b              = {!!}
prepend-step E-Deref-Err E-Error        = E-DerefErr E-Error


prepend-step (E-AssLeft s) (E-Ass rep b b₁) = E-Ass rep (prepend-step s b) b₁
prepend-step (E-AssLeft s) (E-AssOob x b b₁) = E-AssOob x (prepend-step s b) b₁
prepend-step (E-AssLeft s) (E-AssErr b) = E-AssErr (prepend-step s b)
prepend-step (E-AssRight isV s) (E-Ass rep b b₁) = E-Ass rep {!!} {!!}
prepend-step (E-AssRight isV s) (E-AssOob x b b₁) = E-AssOob x {!!} (prepend-step s {!!})
prepend-step (E-AssRight (proj₁ , proj₂) s) (E-AssErr b) = ⊥-elim (proj₂ {!!})
prepend-step (E-AssRed-Suc {ty} {n} {r} {H1} {t} {v} isV eq rep) b with elem? H1 r ty
prepend-step (E-AssRed-Suc isV eq rep) b | inj₁ x = E-Ass {!!} {!!} b
prepend-step (E-AssRed-Suc isV eq rep) b | inj₂ y = ⊥-elim (y rep)
--... | inj₁ x with replace-heap v (inj₁ rep) | replace-result v (inj₁ rep)
--... | rh | rr rewrite (sym eq) = E-Ass ? --{ty} {n} {n} {{!!}} {r} {H1} {H1} {{!!}} {ref r} E-Ref {!!}
--... | rh rewrite (sym eq) with value-of-value {ty} {n} {H1} v
--... | vov = E-Ass {ty} {n} {n} {_} {r} {H1} {H1} {{!!}} {ref r} E-Ref {!!}
-- E-Ass {ty} {n} {n} {{!!}} {r} {H1} {H1} {replace-heap v (inj₁ {!!})} {ref r} {t} {v} E-Ref {!!}
-- ... | inj₁ x with replace-result {n} {H1} v (inj₁ x)
-- --... | rr = {!E-A!}
-- ... | rr  with replace-heap v (inj₁ rep)
-- --Goal: BStep (ref .r <- .t2) .v
-- ... | rh rewrite (sym eq) = E-Ass E-Ref {!!}
--prepend-step (E-AssRed-Suc {v = v} isV eq rep) b | inj₂ y = ⊥-elim (y rep)
prepend-step (E-AssRed-Fail notRep    ) E-Error = {!!}
prepend-step E-Assign-Err1              E-Error = {!!}

prepend-step (E-Seq1 s) (E-Seq x b b₁) = E-Seq x (prepend-step s b) b₁
prepend-step (E-Seq1 s) (E-SeqErr b) = E-SeqErr (prepend-step s b)
prepend-step (E-SeqVal {ty1 = ty1} {t1 = t1} (proj₁ , proj₂)) b with ⌞ t1 , proj₁ ⌟
prepend-step (E-SeqVal {ty1 = .Boolean} (proj₁ , proj₂)) b | vtrue = E-Seq (λ x → proj₂ (verr-is-err {Boolean} {{!vtrue!}} x)) (value-of-value {!vtrue!}) b
prepend-step (E-SeqVal (proj₁ , proj₂)) b | vfalse = {!!}
prepend-step (E-SeqVal (proj₁ , proj₂)) b | vnat x = {!!}
prepend-step (E-SeqVal (proj₁ , proj₂)) b | vref x = {!!}
prepend-step (E-SeqVal (proj₁ , proj₂)) b | verror = ⊥-elim (proj₂ {!!}) -- 
prepend-step E-Seq-Err    E-Error = E-SeqErr E-Error

prepend-step (E-Try-Catch s) (E-TryCat   x b    ) = E-TryCat   x (prepend-step s b)
prepend-step (E-Try-Catch s) (E-TryCatEx b1 b2) = E-TryCatEx (prepend-step s b1) b2
prepend-step (E-Try-Catch-Suc  (proj₁ , proj₂)) b = E-TryCat  {!!}       b
prepend-step (E-Try-Catch-Fail isE            ) b = {!!} --E-TryCatEx (prepend-step {!!} E-Error) b
--prepend-step _ _ = {!!} 

{-
small-to-big : ∀ {ty n m} {H1 : Heap n} {H2 : Heap m} {t : Term ty} {v : Value ty} → 
               Steps {H1 = H1} {H2 = H2} t ⌜ v ⌝ -> BStep {H1 = H1} {H2 = H2} t v
small-to-big [] = value-of-value _
small-to-big (stp :: stps) = prepend-step stp (small-to-big stps)



-}
