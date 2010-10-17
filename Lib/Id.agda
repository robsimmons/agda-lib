{-# OPTIONS --universe-polymorphism #-}

module Lib.Id where

open import Lib.Level

data _≡_ {l : Level} {A : Set l} : A → A → Set l where
  Refl : {a : A} → a ≡ a

{-# BUILTIN EQUALITY _≡_ #-}
{-# BUILTIN REFL Refl #-}

refl : ∀{l} {A : Set l} {a : A} → a ≡ a
refl = Refl

symm : ∀{l} {A : Set l} {a b : A} → a ≡ b → b ≡ a
symm Refl = Refl

_≡≡_ : ∀{l} {A : Set l} {a b c : A} → a ≡ b → b ≡ c → a ≡ c
Refl ≡≡ Refl = Refl

infix 5 _≡_
infixr 5 _≡≡_