{-# OPTIONS --universe-polymorphism #-}

module Lib.Product where 

open import Lib.Level

module Product where

  infixr 0 _,_
  infix 0 ,_
  infixr 10 _×_

  record UnitT {l : LevelT} : Set l where
    constructor <> 
  ⊤ = UnitT {Z}
  Unit0 = UnitT {Z}
  
  {- This is not yet a record, because you can't pattern match records -}
  data Σ {a b} (A : Set a) (B : A → Set b) : Set (Level.max a b) where
    _,_ : (p1 : A) (p2 : B p1) → Σ A B
  Product : ∀{a b} (A : Set a) (B : A → Set b) → Set (Level.max a b)
  Product A B = Σ A B

  fst : ∀{a b} {A : Set a} {B : A → Set b} (p : Σ A B) → A
  fst (p1 , p2) = p1

  snd : ∀{a b} {A : Set a} {B : A → Set b} (p : Σ A B) → B (fst p)
  snd (p1 , p2) = p2

  syntax Σ A (λ x → B) = Σ[ x ∶ A ] B
 
  ∃ : ∀{a b} {A : Set a} → (A → Set b) → Set (Level.max a b)
  ∃ = Σ _

  _×_ : ∀{a b} (A : Set a) (B : Set b) → Set (Level.max a b)
  A × B = Σ[ x ∶ A ] B

  ,_ : ∀{a b} {A : Set a} {B : A → Set b} {x} → B x → ∃ B
  , snd = _ , snd

open Product public
  using (⊤ ; UnitT ; <> ; Unit0 ; 
         Σ ; _,_ ; fst ; snd ; ∃ ; _×_ ; ,_)
  renaming (Product to ProductT)
