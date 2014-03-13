-- Project for Theory of Programming and Types 2014
-- We are going to implement and prove properties about the simply typed λ-language
-- enriched with references.

module Lang where

open import Data.Nat
open import Data.List renaming (_∷_ to _::_)

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

  Heap : Set
  Heap = List (Value unit)       -- references contain only unit

  -- Values contains explicit type information
  data Value : Type -> Set where
    UnitV : Value unit

  -- Reference to a variable, bound during some abstraction.
  data VarRef : Context -> Type -> Set where
    Top : forall {G u} -> VarRef (u :: G) u
    Pop : forall {G u v} -> VarRef G u -> VarRef (v :: G) u

  -- Reference to an heap cell.
  data HeapRef : Heap -> Set where
    Top : forall {H u} -> HeapRef (u :: H)
    Pop : forall {H v} -> HeapRef H -> HeapRef (v :: H) 

  -- A term in the lambda calculus. The language solely consists of
  -- abstractions, applications and variable references.
  data Term : Context -> Heap -> Type -> Set where
    Val : forall {G H ty} -> Value ty -> Term G H ty
    Abs : forall {G H u v} -> Term (u :: G) H v -> Term G H (u => v)
    App : forall {G H u v} -> Term G H (u => v) -> Term G H u -> Term G H v
    Var : forall {G H u} -> VarRef G u -> Term G H u
    New : forall {G H u} -> Term G H u -> Term G (UnitV :: H) (Ref unit)  -- Create new reference
    !_ : forall {G H} -> HeapRef H -> Term G H unit                       -- Deference
    _:=_ : forall {G H} -> (r : HeapRef H) -> Term G H unit -> Term G (insert H r UnitV) unit  -- Assignment

  -- is this really insert? looks more like a replace?
  insert : (h : Heap) -> HeapRef h -> Value unit -> Heap
  insert .(u :: H) (Top {H} {u}) v = v :: H
  insert .(v :: H) (Pop {H} {v} r) v₁ = v :: insert H r v₁
