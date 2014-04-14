module Proofs.CompSound where

open import Base
open import BigStep
open import Denotational
open import Data.Unit using (unit)
open import Data.Nat 
open import Relation.Binary.PropositionalEquality hiding ( [_] )
open import Data.Empty renaming (⊥-elim to contradiction)

--------------------------------------------------------------------------------
-- Big step is Complete and Sound
--------------------------------------------------------------------------------

⇓complete : ∀ {ty n} -> (t : Term ty) -> (H1 : Heap n) -> 
              let < v , H2 > = ⟦ t ⟧ H1 in BStep {H1 = H1} {H2 = H2} t v 
⇓complete true H = E-True
⇓complete false H = E-False
⇓complete error H = E-Error
⇓complete (num x) H = E-Num
⇓complete (iszero t) H with ⟦ t ⟧ H | ⇓complete t H
⇓complete (iszero t) H | < vnat zero , heap > | bstp = E-IsZerZ bstp
⇓complete (iszero t) H | < vnat (suc x) , heap > | bstp = E-IsZerS bstp
⇓complete (iszero t) H | < verror , heap > | bstp = E-IsZerErr bstp
⇓complete (if t then t₁ else t₂) H with ⟦ t ⟧ H | ⇓complete t H
⇓complete (if t then t₁ else t₂) H | < vtrue , heap > | bstp = E-IfTrue bstp (⇓complete t₁ heap)
⇓complete (if t then t₁ else t₂) H | < vfalse , heap > | bstp = E-IfFalse bstp (⇓complete t₂ heap)
⇓complete (if t then t₁ else t₂) H | < verror , heap > | bstp = E-IfErr bstp
⇓complete (new t) H with ⟦ t ⟧ H | ⇓complete t H 
⇓complete (new t) H | < value , heap > | bstp = E-New bstp
⇓complete (! t) H with ⟦ t ⟧ H | ⇓complete t H
⇓complete (! t) H | < vref x , heap > | bstp = E-Deref bstp
⇓complete (! t) H | < verror , heap > | bstp = E-DerefErr bstp
⇓complete (t <- t₁) H with ⟦ t ⟧ H | ⇓complete t H
⇓complete (t <- t₁) H | < vref x , H' > | bstp with ⟦ t₁ ⟧ H' | ⇓complete t₁ H'
⇓complete (t <- t₁) H | < vref x , H' > | bstp | < value , heap > | bstep₁ = {!!}
⇓complete (t <- t₁) H | < verror , heap > | bstp = E-AssErr bstp
⇓complete (ref x) H = E-Ref
⇓complete (try t catch t₁) H with ⟦ t ⟧ H | ⇓complete t H  
⇓complete (try t catch t₁) H | < vtrue , heap > | bstp = {!!}
⇓complete (try t catch t₁) H | < vfalse , heap > | bstp = {!!}
⇓complete (try t catch t₁) H | < vnat x , heap > | bstp = {!!}
⇓complete (try t catch t₁) H | < vref x , heap > | bstp = {!!}
⇓complete (try t catch t₁) H | < verror , heap > | bstp = {!!}
⇓complete (t1 >> t2) H = {!!}

⇓sound : ∀ {ty n m} {H1 : Heap n} {H2 : Heap m} (t : Term ty) (v : Value ty) -> 
         BStep {H1 = H1} {H2 = H2} t v -> ⟦ t ⟧ H1 ≡ < v , H2 >
{-
⇓sound .true     .vtrue     E-True            = refl
⇓sound .false    .vfalse    E-False           = refl
⇓sound .(num m₁) .(vnat m₁) (E-Num {._} {m₁}) = refl
⇓sound .(ref m₁) .(vref m₁) (E-Ref {._} {m₁}) = refl
⇓sound .error    .verror    E-Error           = refl

⇓sound .(if t then t1 else t2) v       (E-IfTrue {._} {._} {n2} {._} {._} {H3} {._} {t} {t1} {t2} b1 b2) with ⟦ t ⟧ H1 | ⇓sound t vtrue b1
...                                                                                                      |    xx       | yy                = {!!}
⇓sound .(if t then t1 else t2) v       (E-IfFalse {._} {._} {n2} {._} {._} {H3} {._} {t} {t1} {t2} b b₁) = {!!}
⇓sound .(if t then t1 else t2) .verror (E-IfErr {._} {._} {._} {._} {._} {t} {t1} {t2} b) = {!!}

⇓sound .(iszero t) .vtrue (E-IsZerZ {._} {._} {._} {._} {t} b) = {!!}
⇓sound .(iszero t) .vfalse (E-IsZerS {._} {._} {._} {._} {t} b) = {!!}
⇓sound .(iszero t) .verror (E-IsZerErr {._} {._} {._} {._} {t} b) = {!!}

⇓sound .(new t) .(vref m) (E-New {ty} {._} {m} {._} {H2} {t} b) = {!!}

⇓sound {ty} {n} {m} {H1} {H2} .(! t) .(lookup r H2) (E-Deref {.ty} {.n} {.m} {r} {.H1} {.H2} {t} b) = {!!}
⇓sound .(! t) .verror (E-DerefErr {._} {._} {._} {._} {._} {t} b) = {!!}

⇓sound .(t1 <- t2) v (E-Ass {._} {._} {n2} {._} {r} {._} {H2} {H3} {t2} t1 rep b b₁) = {!!}
⇓sound .(t1 <- t2) .verror (E-AssOob {._} {._} {._} {n3} {r} {._} {._} {H3} {t2} t1 x b) = {!!}
⇓sound .(t1 <- t2) .verror (E-AssErr {._} {._} {._} {._} {._} {t2} t1 b) = {!!}

⇓sound .(t1 >> t2) v (E-Seq {ty1} {._} {._} {n2} {._} {._} {H3} {._} {t1} {v1} {t2} x b b₁) = {!!}
⇓sound .(t1 >> t2) .verror (E-SeqErr {ty1} {._} {._} {._} {._} {._} {t1} {t2} b) = {!!}

⇓sound .(try t1 catch t2) v (E-TryCat {._} {._} {._} {._} {._} {t1} {t2} x b) = {!!}
⇓sound .(try t1 catch t2) v (E-TryCatEx {._} {._} {n2} {._} {._} {H3} {._} {t1} {t2} b b₁) = {!!}
-}

⇓sound .true .vtrue E-True = refl
⇓sound .false .vfalse E-False = refl
⇓sound (num n) (vnat .n) E-Num = refl
⇓sound {H1 = H1} (iszero t) .vtrue (E-IsZerZ bstp) with ⟦ t ⟧ H1 | ⇓sound t (vnat zero) bstp
⇓sound (iszero t) .vtrue (E-IsZerZ bstp) | (< vnat 0 , H2 >) | refl = refl
⇓sound {H1 = H1} (iszero t) .vfalse (E-IsZerS {n = n} bstp) with ⟦ t ⟧ H1 | ⇓sound t (vnat (suc n)) bstp
⇓sound (iszero t) .vfalse (E-IsZerS bstp) | (< vnat (suc n₁) , H2 >) | refl = refl

⇓sound {H1 = H1} (if t then t1 else t2) v (E-IfTrue bstp bstp₁) with ⟦ t ⟧ H1 | ⇓sound t vtrue bstp
⇓sound (if t then t1 else t2) v (E-IfTrue bstp bstp₁) | < vtrue , H2 > | refl = ⇓sound t1 v bstp₁
⇓sound {H1 = H1} (if t then t1 else t2) v (E-IfFalse bstp bstp₁) with ⟦ t ⟧ H1 | ⇓sound t vfalse bstp 
⇓sound (if t then t1 else t2) v (E-IfFalse bstp bstp₁) | < vfalse , H2 > | refl = ⇓sound t2 v bstp₁
⇓sound {H1 = H1} (if t then t1 else t2) .verror (E-IfErr bstp) with ⟦ t ⟧ H1 | ⇓sound t verror bstp
⇓sound (if t then t1 else t2) .verror (E-IfErr bstp) | < verror , H2 > | refl = refl 

⇓sound {H1 = H1} (new t) (vref 0) (E-New bstp) with ⟦ t ⟧ H1 | ⇓sound t _ bstp
⇓sound (new t) (vref zero) (E-New bstp) | < v , H2 > | refl = refl 
⇓sound {H1 = H1} {H2 = H2} .(! t) .(lookup r H2) (E-Deref {r = r} {t = t} bstp) with  ⟦ t ⟧ H1 | ⇓sound t (vref r) bstp
⇓sound .(! t) .(lookup r H2) (E-Deref {t = t} bstp) | < vref r , H2 > | refl = refl
⇓sound {H1 = H1} (! t) .verror (E-DerefErr bstp) with  ⟦ t ⟧ H1 | ⇓sound t verror bstp
⇓sound {H1 = H1} (! t) .verror (E-DerefErr bstp) | < verror , H2 > | refl = refl 

--⇓sound {H1 = H1} (ref r <- t) v (E-Ass  rep bstp1 bstp2) = {!!} -- E-AssRed comes here and makes things horrible
⇓sound ._ _ (E-Ass {t1 = error {._}              } _ _ _) = {!!}
⇓sound ._ _ (E-Ass {t1 = if_then_else_ {._} _ _ _} _ _ _) = {!!}
⇓sound ._ _ (E-Ass {t1 = new {._} _              } _ _ _) = {!!}
⇓sound ._ _ (E-Ass {t1 = !_ {._} _               } _ _ _) = {!!}
⇓sound ._ _ (E-Ass {t1 = _<-_ {._} _ _           } _ _ _) = {!!}
⇓sound ._ _ (E-Ass {t1 = try_catch_ {._} _ _     } _ _ _) = {!!}
⇓sound ._ _ (E-Ass {t1 = _>>_ {_} {._} _ _       } _ _ _) = {!!}
⇓sound ._ _ (E-Ass {t1 = ref {._} _              } _ _ _) = {!!}

⇓sound .error .verror E-Error = refl
⇓sound (ref .m₁) (vref m₁) E-Ref = refl
⇓sound {H1 = H1} (t1 >> t2) v (E-Seq isG stp1 stp2) with ⟦ t1 ⟧ H1 | ⇓sound t1 _ stp1
⇓sound (t1 >> t2) v (E-Seq notE stp1 stp2) | < vtrue , H2 > | refl with ⟦ t2 ⟧ H2 | ⇓sound t2 _ stp2
⇓sound (t1 >> t2) v (E-Seq notE stp1 stp2) | < vtrue , H3 > | refl | < .v , H2 > | refl = refl
⇓sound (t1 >> t2) v (E-Seq notE stp1 stp2) | < vfalse , H2 > | refl with  ⟦ t2 ⟧ H2 | ⇓sound t2 _ stp2
⇓sound (t1 >> t2) v (E-Seq notE stp1 stp2) | < vfalse , H2 > | refl | < .v , H3 > | refl = refl
⇓sound (t1 >> t2) v (E-Seq notE stp1 stp2) | < vnat x , H2 > | refl with ⟦ t2 ⟧ H2 | ⇓sound t2 _ stp2
⇓sound (t1 >> t2) v (E-Seq notE stp1 stp2) | < vnat x , H2 > | refl | < .v , H3 > | refl = refl
⇓sound (t1 >> t2) v (E-Seq notE stp1 stp2) | < vref x , H2 > | refl with ⟦ t2 ⟧ H2 | ⇓sound t2 _ stp2
⇓sound (t1 >> t2) v (E-Seq notE stp1 stp2) | < vref x , H2 > | refl | < .v , H3 > | refl = refl
⇓sound (t1 >> t2) v (E-Seq notE stp1 stp2) | < verror , H2 > | refl = contradiction (notE unit)

⇓sound {H1 = H1} (t1 >> t2) .verror (E-SeqErr bstp) with ⟦ t1 ⟧ H1 | ⇓sound t1 verror bstp
⇓sound (t1 >> t2) .verror (E-SeqErr bstp) | < verror , H2 > | refl = refl

⇓sound {H1 = H1} (iszero t) .verror (E-IsZerErr b) with ⟦ t ⟧ H1        | ⇓sound t verror b
...                                                | .(< verror , _ >)  | refl              = refl

⇓sound {H1 = H1} (new t) (vref m) (E-New c) with ⟦ t ⟧ H1      | ⇓sound t _ c
...                                         |    .(< _ , _ >)  | refl         = refl

⇓sound                    {H1 = H1} (try t1 catch t2) v        (E-TryCat a b) with ⟦ t1 ⟧ H1       | ⇓sound t1 v b
⇓sound {.Boolean} {n} {m} {H1} {H2} (try t1 catch t2) vtrue    (E-TryCat a b) | .(< vtrue  , H2 >) | refl          = refl
⇓sound {.Boolean} {n} {m} {H1} {H2} (try t1 catch t2) vfalse   (E-TryCat a b) | .(< vfalse , H2 >) | refl          = refl
⇓sound {.Natural} {n} {m} {H1} {H2} (try t1 catch t2) (vnat x) (E-TryCat a b) | .(< vnat x , H2 >) | refl          = refl
⇓sound {.(Ref _)} {n} {m} {H1} {H2} (try t1 catch t2) (vref x) (E-TryCat a b) | .(< vref x , H2 >) | refl          = refl
⇓sound {ty      } {n} {m} {H1} {H2} (try t1 catch t2) verror   (E-TryCat a b) | .(< verror , H2 >) | refl          = contradiction (a unit)

⇓sound {H1 = H1} (try t1 catch t2) v (E-TryCatEx a b) with ⟦ t1 ⟧ H1
⇓sound (try t1 catch t2) v (E-TryCatEx a b) | < value , heap > = {!!}

⇓sound ._ ._ (E-AssErr {t1 = error {._}              } _) = {!!}
⇓sound ._ ._ (E-AssErr {t1 = if_then_else_ {._} _ _ _} _) = {!!}
⇓sound ._ ._ (E-AssErr {t1 = new {._} _              } _) = {!!}
⇓sound ._ ._ (E-AssErr {t1 = !_ {._} _               } _) = {!!}
⇓sound ._ ._ (E-AssErr {t1 = _<-_ {._} _ _           } _) = {!!}
⇓sound ._ ._ (E-AssErr {t1 = try_catch_ {._} _ _     } _) = {!!}
⇓sound ._ ._ (E-AssErr {t1 = _>>_ {_} {._} _ _       } _) = {!!}
⇓sound ._ ._ (E-AssErr {t1 = ref {._} _              } _) = {!!}

⇓sound ._ ._ (E-AssOob {._} {._} _ _ k) = {!!}
