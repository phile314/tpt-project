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
open import Denotational
open import Relation.Binary.HeterogeneousEquality

--open import Proofs.CompSound

open import Relation.Binary.PropositionalEquality hiding ( [_] ) -- remove

--------------------------------------------------------------------------------
-- Conversion between BigStep and SmallStep
--------------------------------------------------------------------------------


-- Lemmas used for small-to-big
-- Converstion from big- to small-step representations.

err-is-verr : ∀ {ty} {v : Value ty} -> isError ⌜ v ⌝ -> isVError v
err-is-verr {.Boolean} {vtrue} ()
err-is-verr {.Boolean} {vfalse} ()
err-is-verr {.Natural} {vnat x} ()
err-is-verr {Ref ty} {vref x} ()
err-is-verr {ty} {verror} err = unit


verr-is-err : ∀ {ty} {t : Term ty} -> (isV : isValue t) -> isVError (⌞ t , isV ⌟) -> isError t
verr-is-err = {!!}

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

-- BStep from value terms to values are Heap invariant
val-of-val-expr : ∀ {ty n m k} {H1 : Heap n} {H2 : Heap m} {v : Value ty} {t : Term ty} -> (isValue t) -> BStep {H1 = H1} {H2 = H2} t v -> H1 ≅ H2
val-of-val-expr = {!!}

val-of-val-inv : forall {ty n m k} {H1 : Heap n} {H2 : Heap m} {v : Value ty} {t : Term ty} -> (isValue t) -> BStep {H1 = H1} {H2 = H2} t v -> (H3 : Heap k) -> BStep {H1 = H3} {H2 = H3} t v
val-of-val-inv isV E-True H = E-True
val-of-val-inv isV E-False H = E-False
val-of-val-inv isV E-Num H = E-Num
val-of-val-inv isV E-Ref H = E-Ref
val-of-val-inv isV E-Error H = E-Error
val-of-val-inv () (E-IfTrue b b₁) H
val-of-val-inv () (E-IfFalse b b₁) H
val-of-val-inv () (E-IfErr b) H
val-of-val-inv () (E-IsZerZ b) H
val-of-val-inv () (E-IsZerS b) H
val-of-val-inv () (E-IsZerErr b) H
val-of-val-inv () (E-New b) H
val-of-val-inv () (E-Deref b) H
val-of-val-inv () (E-DerefErr b) H
val-of-val-inv () (E-Ass rep b b₁) H
val-of-val-inv () (E-AssOob x b b₁) H
val-of-val-inv () (E-AssErr b) H
val-of-val-inv () (E-Seq x b b₁) H
val-of-val-inv () (E-SeqErr b) H
val-of-val-inv () (E-TryCat x b) H
val-of-val-inv () (E-TryCatEx b b₁) H

value-of-term : ∀ {ty n} {H : Heap n} {t : Term ty} -> (isV : isValue t) -> BStep {H1 = H} {H2 = H} t (⌞ t , isV ⌟)
value-of-term {.Boolean} {n} {H} {true} is = E-True
value-of-term {.Boolean} {n} {H} {false} is = E-False
value-of-term {ty} {n} {H} {error} is = E-Error
value-of-term {.Natural} {n} {H} {num x} is = E-Num
value-of-term {.Boolean} {n} {H} {iszero t} ()
value-of-term {ty} {n} {H} {if t then t₁ else t₂} ()
value-of-term {Ref ty} {n} {H} {new t} ()
value-of-term {ty} {n} {H} { ! t} ()
value-of-term {ty} {n} {H} {t <- t₁} ()
value-of-term {(Ref ty)} {n} {H} {ref x} is = E-Ref
value-of-term {ty} {n} {H} {try t catch t₁} ()
value-of-term {ty} {n} {H} {t >> t₁} ()

err-eq : ∀ {ty} {t : Term ty} -> (isError t) -> t ≡ error
err-eq {.Boolean} {true} ()
err-eq {.Boolean} {false} ()
err-eq {ty} {error} unit = refl
err-eq {.Natural} {num x} ()
err-eq {.Boolean} {iszero t} ()
err-eq {ty} {if t then t₁ else t₂} ()
err-eq {Ref ty} {new t} ()
err-eq {ty} { ! t} ()
err-eq {ty} {t <- t₁} ()
err-eq {Ref ty} {ref x} ()
err-eq {ty} {try t catch t₁} ()
err-eq {ty} {t >> t₁} ()

h : ∀ {ty r m n} {H1 : Heap m} {H2 : Heap n} -> Elem H1 r ty -> H1 ≅ H2 -> Elem H2 r ty
h {ty} {r} {.0} {_} {Nil} () eq
h {ty} {r} {suc n₁} {.0} {Cons v H1} {Nil} el ()
h {ty} {.0} {suc .n} {suc n} {Cons .v₁ .H2} {Cons v₁ H2} (Top {.n} {.ty} {.v₁} {.H2}) refl = Top {n} {ty} {v₁} {H2}
h {ty} {(suc i)} {suc .n} {suc n} {Cons .v₁ .H2} {Cons {ty'} v₁ H2} (Pop el) refl with h {H1 = H2} {H2 = H2} el refl
... | rec = Pop {n} {ty} {i} {ty'} {v₁} {H2} rec
--h {ty} {suc i} {suc .n} {suc n} {Cons .v₁ .H2} {Cons v₁ H2} (Pop e) refl = {!!}


-- Combining a single small step with a big step.

prepend-step : forall {ty n1 n2 n3} {H1 : Heap n1} {H2 : Heap n2} {H3 : Heap n3} {t1 t2 : Term ty} {v : Value ty} -> 
               Step {H1 = H1} {H2 = H2} t1 t2 -> BStep {H1 = H2} {H2 = H3} t2 v -> BStep {H1 = H1} {H2 = H3} t1 v

-- this should have a better name....
g : ∀ {ty n m k l} {H1 : Heap n} {H2 : Heap m} {H3 : Heap k} {H4 : Heap l} {t1 t2 : Term ty} {v : Value ty}
            -> {t3 : Term (Ref ty)} -> {v3 : Value (Ref ty)}
            -> BStep {H1 = H2} {H2 = H3}  t3 v3 -> isValue t3 -> Step {H1 = H1} {H2 = H2} t1 t2
            -> BStep {H1 = H3} {H2 = H4} t2 v -> BStep {H1 = H1} {H2 = H4} (t1) v


g E-Ref isV b2 b3 = prepend-step b2 b3
g E-Error isV b2 b3 = prepend-step b2 b3
g (E-IfTrue b1 b2) () b3 b4
g (E-IfFalse b1 b2) () b3 b4
g (E-IfErr b1) () b2 b3
g (E-New b1) () b2 b3
g (E-Deref b1) () b2 b3
g (E-DerefErr b1) () b2 b3
g (E-Ass rep b1 b2) () b3 b4
g (E-AssOob x b1 b2) () b3 b4
g (E-AssErr b1) () b2 b3
g (E-Seq x b1 b2) () b3 b4
g (E-SeqErr b1) () b2 b3
g (E-TryCat x b1) () b2 b3
g (E-TryCatEx b1 b2) () b3 b4

k : ∀ {ty} {t : Term ty} {isV : isValue t} -> isVError ⌞ t , isV ⌟ -> isError t
k {.Boolean} {true} ()
k {.Boolean} {false} ()
k {ty} {error} unit = unit
k {.Natural} {num x} ()
k {.Boolean} {iszero t} {()} isVE
k {ty} {if t then t₁ else t₂} {()} isVE
k {(Ref ty)} {new t} {()} isVE
k {ty} { ! t} {()} isVE
k {ty} {t <- t₁} {()} isVE
k {Ref ty} {ref x} ()  
k {ty} {t >> t₁} {()} isVE
k {ty} {try t1 catch t2} {()} isVE

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
prepend-step {H1 = H1} {H2 = .H2} {H3 = .(replace H4 rep _)} (E-AssRight {H1 = .H1} {H2 = .H2} (isV , notE) s) (E-Ass {H1 = H2} {H2 = H3} {H3 = H4} rep bstp bstp₁) with val-of-val-inv isV bstp H1
... | bstp' = E-Ass rep bstp' (g bstp isV s bstp₁)
prepend-step {H1 = H1} (E-AssRight (isV , notE) s) (E-AssOob x bstp bstp₁) with val-of-val-inv isV bstp H1
... | bstp' = E-AssOob x bstp' (g bstp isV s bstp₁)
prepend-step (E-AssRight (proj₁ , proj₂) s) (E-AssErr b) = ⊥-elim (proj₂ (z proj₁ b))
  where z : ∀ {ty n m} {t : Term ty} {H1 : Heap n} {H2 : Heap m} -> isValue t -> BStep {H1 = H1} {H2 = H2} t verror -> isError t
        z {.Boolean} {n} {m} {true} isV ()
        z {.Boolean} {n} {m} {false} isV ()
        z {ty} {n} {m} {error} isV b₁ = unit
        z {.Natural} {n} {m} {num x} isV ()
        z {.Boolean} {n} {m} {iszero t} () b₁
        z {ty} {n} {m} {if t then t₁ else t₂} () b₁
        z {(Ref ty)} {n} {m} {new t} () b₁
        z {ty} {n} {m} { ! t} () b₁
        z {ty} {n} {m} {t <- t₁} () b₁
        z {(Ref ty)} {n} {m} {ref x} isV ()
        z {ty} {n} {m} {try t catch t₁} () b₁
        z {ty} {n} {m} {t >> t₁} () b₁
prepend-step (E-AssRed-Suc {ty} {n} {r} {H1} {t} {v} isV eq rep) b = E-Ass {!!} (value-of-value (vref r)) {!!}
--  where h : ∀ {ty r m n} {H1 : Heap m} {H2 : Heap n} -> Elem H1 r ty -> H1 ≅ H2 -> Elem H2 r ty
--        h e eq = {!eq!}
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
prepend-step {ty} (E-AssRed-Fail {r = r} {t = t} {isV = isV} notRep    ) E-Error = E-AssOob {v = ⌞ t , isV ⌟} notRep (value-of-value (vref {ty} r)) (value-of-term isV)
prepend-step E-Assign-Err1              E-Error = E-AssErr E-Error

prepend-step (E-Seq1 s) (E-Seq x b b₁) = E-Seq x (prepend-step s b) b₁
prepend-step (E-Seq1 s) (E-SeqErr b) = E-SeqErr (prepend-step s b)
prepend-step (E-SeqVal {ty1 = ty1} {t1 = t1} (proj₁ , proj₂)) b = E-Seq (λ x → proj₂ (k x)) (value-of-term proj₁) b
-- with ⟦ t1 ⟧ {!!} -- with ⌞ t1 , proj₁ ⌟
--prepend-step (E-SeqVal (proj₁ , proj₂)) b | Denotational.< value , heap > = E-Seq (λ x → proj₂ (verr-is-err {_} {{!value!}} {!!})) (value-of-value _) b
prepend-step E-Seq-Err    E-Error = E-SeqErr E-Error

prepend-step (E-Try-Catch s) (E-TryCat   x b    ) = E-TryCat   x (prepend-step s b)
prepend-step (E-Try-Catch s) (E-TryCatEx b1 b2) = E-TryCatEx (prepend-step s b1) b2
prepend-step (E-Try-Catch-Suc  (proj₁ , proj₂)) b = E-TryCat  (λ x → proj₂ (z proj₁ b x))       b
  where z : ∀ {ty n m} {H1 : Heap n} {H2 : Heap m} {v : Value ty} {t : Term ty} -> isValue t -> (BStep {H1 = H1} {H2 = H2} t v) -> isVError v -> isError t
        z {.Boolean} {.m} {m} {.H2} {H2} {.vtrue} {true} isV E-True ()
        z {.Boolean} {.m} {m} {.H2} {H2} {.vfalse} {false} isV E-False ()
        z {ty} {n} {m} {H1} {H2} {v} {error} isV b₁ isVE = unit
        z {.Natural} {.m} {m} {.H2} {H2} {.(vnat x)} {num x} isV E-Num ()
        z {.Boolean} {n} {m} {H1} {H2} {v} {iszero t} () b₁ isVE
        z {ty} {n} {m} {H1} {H2} {v} {if t then t₁ else t₂} () b₁ isVE
        z {(Ref ty)} {n} {m} {H1} {H2} {v} {new t} () b₁ isVE
        z {ty} {n} {m} {H1} {H2} {v} { ! t} () b₁ isVE
        z {ty} {n} {m} {H1} {H2} {v} {t <- t₁} () b₁ isVE
        z {Ref ty} {.m} {m} {.H2} {H2} {.(vref x₁)} {ref x₁} isV E-Ref ()
        z {ty} {n} {m} {H1} {H2} {v} {try t catch t₁} () b₁ isVE
        z {ty} {n} {m} {H1} {H2} {v} {t >> t₁} () b₁ isVE
prepend-step {t1 = try t catch t'} (E-Try-Catch-Fail isE            ) b rewrite err-eq isE = E-TryCatEx (value-of-value verror) b
--prepend-step _ _ = {!!} 

{-
small-to-big : ∀ {ty n m} {H1 : Heap n} {H2 : Heap m} {t : Term ty} {v : Value ty} → 
               Steps {H1 = H1} {H2 = H2} t ⌜ v ⌝ -> BStep {H1 = H1} {H2 = H2} t v
small-to-big [] = value-of-value _
small-to-big (stp :: stps) = prepend-step stp (small-to-big stps)



-}
