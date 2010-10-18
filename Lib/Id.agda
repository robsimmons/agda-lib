{-# OPTIONS --universe-polymorphism #-}

module Lib.Id where

open import Lib.Level

module Id where

  infix 5 _≡_
  infixr 5 _≡≡_
  data _≡_ {l : LevelT} {A : Set l} : A → A → Set l where
    Refl : {a : A} → a ≡ a
  IdT : ∀ {l} {A : Set l} → A → A → Set l
  IdT x y = x ≡ y

  {-# BUILTIN EQUALITY IdT #-}
  {-# BUILTIN REFL Refl #-}

  refl : ∀{l} {A : Set l} {a : A} → a ≡ a
  refl = Refl

  symm : ∀{l} {A : Set l} {a b : A} → a ≡ b → b ≡ a
  symm Refl = refl

  trans : ∀{l} {A : Set l} {a b c : A} → a ≡ b → b ≡ c → a ≡ c
  trans Refl Refl = refl

  _≡≡_ : ∀{l} {A : Set l} {a b c : A} → a ≡ b → b ≡ c → a ≡ c
  Refl ≡≡ Refl = Refl

open Id public 
  using (IdT ; Refl ; _≡_ ; refl ; symm ; trans ; _≡≡_)