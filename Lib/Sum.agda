{-# OPTIONS --universe-polymorphism #-}

module Lib.Sum where 

open import Lib.Level
open import Lib.Product

module Sum where

  data VoidT {l : LevelT} : Set l where
  ⊥ = VoidT {Z}
  Void0 = VoidT {Z}

  abort : ∀{a b} {A : Set a} → VoidT {b} → A
  abort ()

  data _+_ {l : LevelT} (A : Set l) (B : Set l) : Set l where
    Inl : A → A + B
    Inr : B → A + B
  SumT : ∀ {l} (A : Set l) (B : Set l) → Set l
  SumT A B = A + B
  Sum0 = SumT {Z}

  case : ∀{a b} {A B : Set a} {C : Set b} → A + B → (A → C) → (B → C) → C
  case (Inl x) f g = f x
  case (Inr x) f g = g x 

open Sum public
  using (⊥ ; VoidT ; Void0 ; abort ; Inl ; Inr ; SumT ; Sum0 ; _+_ ; case) 
