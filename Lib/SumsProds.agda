{-# OPTIONS --universe-polymorphism #-}

module Lib.SumsProds where 

open import Lib.Level

module Prods where

  record Unit {l : Level} : Set l where
    constructor <> 
  Unit0 = Unit {Z}
  
  record Σ {a b} (A : Set a) (B : A → Set b) : Set (max a b) where
    constructor _,_
    field
      fst : A
      snd : B fst

  open Σ public

  syntax Σ A (λ x → B) = Σ[ x ∶ A ] B
 
  ∃ : ∀{a b} {A : Set a} → (A → Set b) → Set (max a b)
  ∃ = Σ _

  _×_ : ∀{a b} (A : Set a) (B : Set b) → Set (max a b)
  A × B = Σ[ x ∶ A ] B

  infixr 0 _,_
  infix 0 ,_
  infixr 10 _×_

  ,_ : ∀{a b} {A : Set a} {B : A → Set b} {x} → B x → ∃ B
  , y = _ , y

module Sums where

  data Void {l : Level} : Set l where
  Void0 = Void {Z}

  data _+_ {l : Level} (a : Set l) (b : Set l) : Set l where
    Inl : a → a + b
    Inr : b → a + b
  Either :  {l : Level} (a : Set l) (b : Set l) → Set l
  Either a b = a + b
  Either0 = _+_ {Z}

  abort : ∀{a b} {A : Set a} → Void {b} → A
  abort ()
