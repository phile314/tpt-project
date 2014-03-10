-- Project for Theory of Programming and Types 2014
-- We are going to implement and prove properties about the simply typed λ-language
-- enriched with references.

module Lang where

open import Data.Nat
open import Data.List renaming (_∷_ to _::_)
open import Data.Fin

-- Types supported
data Type : Set where
  unit : Type                    -- Unit type
  _=>_ : Type -> Type -> Type    -- Functions
  Ref  : Type -> Type            -- Reference type

-- Type context: the top of this list is the type of the innermost
-- abstraction variable, the next element is the type of the next
-- variable, and so on.
Context : Set
Context = List Type

mutual

  -- Vec-like unbounded heap. 
  -- In a Heap n, n is the first position available to be allocated in a reference.
  data Heap : ℕ  -> Set where
    Empty : Heap 0
    Alloc : {n : ℕ} -> Value unit -> Heap n -> Heap (suc n)

  -- Values contains explicit type information
  data Value : Type -> Set where
    UnitV : Value unit

  -- Reference to a variable, bound during some abstraction.
  data VarRef : Context -> Type -> Set where
    Top : forall {G u} -> VarRef (u :: G) u
    Pop : forall {G u v} -> VarRef G u -> VarRef (v :: G) u

  -- Reference to an heap cell.
  data HeapRef : {n : ℕ} -> Fin n -> Heap n -> Set where
    Elem : {n : ℕ} -> (i : Fin n) -> (H : Heap n) -> HeapRef i H

  data Term : Context -> (n : ℕ) -> Heap n -> Type -> Set where
    Abs : forall {G n H u v} -> Term (u :: G) n H v -> Term G n H (u => v)
    App : forall {G n H u v} -> Term G n H (u => v) -> Term G n H u -> Term G n H v
    Var : forall {G n H u} -> VarRef G u -> Term G n H u
    New : forall {G n H u} -> Term G n H u -> Term G (suc n) (Alloc UnitV H ) (Ref unit)  -- Create new reference
    !_ : forall {G n H i} -> HeapRef i H -> Term G n H unit                               -- Deference
    -- _:=_ : forall {G n H i} -> (r : HeapRef i H) -> (Term G n H unit) -> Term G n (insert H r UnitV) unit

  -- insert : forall {i n} (H : Heap n) -> HeapRef i H -> Value unit -> H
  -- insert v r h = ? 
