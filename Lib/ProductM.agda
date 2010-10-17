{-# OPTIONS --universe-polymorphism #-}

module Lib.ProductM where 

open import Lib.LevelM

module Product where

  record Unit {l : LevelT} : Set l where
    constructor <> 
  Unit0 = Unit {Z}
  
  {- This is not yet a record, because you can't pattern match records -}
  data Product {a b} (A : Set a) (B : A → Set b) : Set (Level.max a b) where
    _,_ : (p1 : A) (p2 : B p1) → Product A B
  Σ : ∀{a b} (A : Set a) (B : A → Set b) → Set (Level.max a b)
  Σ A B = Product A B

  fst : ∀{a b} {A : Set a} {B : A → Set b} (p : Σ A B) → A
  fst (p1 , p2) = p1

  snd : ∀{a b} {A : Set a} {B : A → Set b} (p : Σ A B) → B (fst p)
  snd (p1 , p2) = p2

  syntax Σ A (λ x → B) = Σ[ x ∶ A ] B
 
  ∃ : ∀{a b} {A : Set a} → (A → Set b) → Set (Level.max a b)
  ∃ = Σ _

  _×_ : ∀{a b} (A : Set a) (B : Set b) → Set (Level.max a b)
  A × B = Σ[ x ∶ A ] B

  infixr 0 _,_
  infix 0 ,_
  infixr 10 _×_

  ,_ : ∀{a b} {A : Set a} {B : A → Set b} {x} → B x → ∃ B
  , snd = _ , snd

open Product public
  using (Unit ; <> ; Unit0 ; Σ ; _,_ ; fst ; snd ; ∃ ; _×_ ; ,_)
  renaming (Product to ProductT)

