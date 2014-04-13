module Proofs.HeapTypePres where

open import Base
open import SmallStep
open import BigStep
open import Denotational
open import Data.Unit using (unit)
open import Data.Sum
open import Data.Product using ( ∃ ; _,_)
open import Data.Nat 
open import Relation.Binary.PropositionalEquality hiding ( [_] )
open import Relation.Nullary
open import Data.Empty

data TypePres : ∀ {n m} -> Heap m -> Heap n -> Set where
  -- The empty heap always preserves types
  Base  : TypePres Nil Nil
  -- If we overwrite a position with a value of the same type, we preserve shape as well.
  Write : ∀ {n ty} {v : Value ty} -> (H1 H2 : Heap n) -> (tp : TypePres H1 H2) -> (v' : Value ty) -> TypePres (Cons v H1) (Cons v' H2)
  -- If we append something, shape is also preserved.
  Grow  : ∀ {n ty} -> (H : Heap n) -> (v : Value ty) -> TypePres H (append H v)

eq=>TypePres : ∀ {n} -> (H : Heap n) -> TypePres H H
eq=>TypePres Nil = Base
eq=>TypePres (Cons v H) = Write H H (eq=>TypePres H) v
--Cons (eq=>TypePres H) v

h-pres-replace : ∀ {n r ty} {H : Heap n} {v : Value ty} -> (e : Elem H r ty) -> TypePres H (replace H  e v)
h-pres-replace {suc n} .{zero} {ty} {Cons v H} {v'} Top = Write H H (eq=>TypePres H) v'
h-pres-replace {suc n} {suc i} {_} {Cons v H} {v'} (Pop e) = Write H (replace H e v') (h-pres-replace e) v

h-pres : ∀ {n m ty} (H1 : Heap n) (H2 : Heap m) {t t' : Term ty} -> Step {H1 = H1} {H2 = H2} t t' -> TypePres H1 H2
h-pres .H2 H2 E-IsZeroZero = eq=>TypePres H2
h-pres .H2 H2 E-IsZeroSucc = eq=>TypePres H2
h-pres H1 H2 (E-IsZero s) = h-pres H1 H2 s
h-pres .H2 H2 E-IfTrue = eq=>TypePres H2
h-pres .H2 H2 E-IfFalse = eq=>TypePres H2
h-pres H1 H2 (E-If s) = h-pres H1 H2 s
h-pres H1 H2 (E-New s) = h-pres H1 H2 s
h-pres H1 .(append H1 v) (E-NewVal {ty} {n} {.H1} {v} eq) = Grow H1 v
h-pres H1 H2 (E-Deref s) = h-pres H1 H2 s
h-pres .H2 H2 E-DerefVal = eq=>TypePres H2
h-pres H1 H2 (E-AssLeft s) = h-pres H1 H2 s
h-pres H1 H2 (E-AssRight isV s) = h-pres H1 H2 s
h-pres H1 .(replace H1 rep v) (E-AssRed-Suc {ty} {m} {r} {.H1} {t'} {v} isV eq rep) = h-pres-replace rep
h-pres .H2 H2 (E-AssRed-Fail notRep) = eq=>TypePres H2
h-pres H1 H2 (E-Try-Catch s) = h-pres H1 H2 s
h-pres .H2 H2 (E-Try-Catch-Suc x) = eq=>TypePres H2
h-pres .H2 H2 (E-Try-Catch-Fail isE) = eq=>TypePres H2
h-pres .H2 H2 E-IsZero-Err = eq=>TypePres H2
h-pres .H2 H2 E-If-Err = eq=>TypePres H2
h-pres .H2 H2 E-Deref-Err = eq=>TypePres H2
h-pres .H2 H2 E-Assign-Err1 = eq=>TypePres H2
h-pres H1 H2 (E-Seq1 stp) = h-pres H1 H2 stp
h-pres .H2 H2 (E-SeqVal isV) = eq=>TypePres H2
h-pres .H2 H2 (E-Seq-Err) = eq=>TypePres H2
