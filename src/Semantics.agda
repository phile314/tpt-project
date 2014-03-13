
module Semantics where

open import Data.List
open import Lang

-- is the term normal form appropriate here?
data IsNF : {ctx : Context} {h : Heap} {ty : Type} -> Term {!!} {!!} ty -> Set where
--  is-nf : forall {ctx h ty} -> (t : Term ctx h ty) -> IsNF {ctx} {h} {ty} t

data IsValue : {ctx : Context} {H : Heap} {ty : Type} -> Term ctx H ty -> Set where
  is-value : forall {ctx H ty} -> Value ty -> IsValue {!!}

lookupHeap : {ctx : Context} {H : Heap} (hr : HeapRef H) -> Term ctx H unit
lookupHeap {ctx} {[]} ()
lookupHeap {ctx} {x ∷ H} Top = Val x
lookupHeap {ctx} {x ∷ H} (Pop hr) = {!!} --lookupHeap {ctx} {H} {!!}

-- Small-step semantics

data Step : forall {ctx1 ctx2 H1 H2 ty} -> Term ctx1 H1 ty -> Term ctx2 H2 ty -> Set where
  E-Abs :  Step {!!} {!!}

  -- how are we going to evaluate functions? i think there is something about that in the lesson notes
  E-App-Fun : {ctx : Context} {H : Heap} {ty1 ty2 : Type} {t1 t1' : Term ctx H (ty1 => ty2)}
              {t2 : Term ctx H ty1} -> Step t1 t1' -> Step (App t1 t2) (App t1' t2)

  E-App-App : {ctx : Context} {H : Heap} {ty1 ty2 : Type} {t1 : Term ctx H (ty1 => ty2)}
              {t2 : Term ctx H ty1} -> IsNF t1 -> IsNF t2 -> Step {!!} {!!}

  E-Ref-New : {ctx : Context} {H1 H2 : Heap} {t : Term ctx H1 unit}
              -> IsNF {ctx} {H1} t -> Step (New t) (Val {ctx} {insert H1 {!!} {!!}} {!!})

  E-Ref-De  :   {ctx : Context} {H : Heap} {hr : HeapRef H}
              -> Step {ctx} {ctx} {H} {H} {unit} (! hr) (lookupHeap hr)

  -- not sure if this one is really needed. It says that values are invariant under
  -- context / heap transformations
  E-ctx-heap : {ctx1 ctx2 : Context} {H1 H2 : Heap} {ty : Type} {t1 : Term ctx1 H1 ty}
               {t2 : Term ctx2 H2 ty} -> IsValue t1 -> Step t1 t2
