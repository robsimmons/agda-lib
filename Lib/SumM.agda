{-# OPTIONS --universe-polymorphism #-}

module Lib.SumM where 

open import Lib.LevelM
open import Lib.ProductM

module Sum where

  data Void {l : LevelT} : Set l where
  Void0 = Void {Z}

  abort : ∀{a b} {A : Set a} → Void {b} → A
  abort ()

  data Sum {l : LevelT} (A : Set l) (B : Set l) : Set l where
    Inl : A → Sum A B
    Inr : B → Sum A B
  _+_ :  {l : LevelT} (A : Set l) (B : Set l) → Set l
  A + B = Sum A B
  Sum0 = Sum {Z}

  case : ∀{a b} {A B : Set a} {C : Set b} → A + B → (A → C) → (B → C) → C
  case (Inl x) f g = f x
  case (Inr x) f g = g x 

open Sum public
  using (Void ; Void0 ; Sum ; Sum0 ; _+_ ; case) 