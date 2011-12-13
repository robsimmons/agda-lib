-- The propositions of Infon Logic (also instantiates contexts)

open import Prelude hiding (⊤)
open import Infon.Judgments

module Infon.Core where

module CORE 
   (Prin : Set)
   (_≡?_ : (p q : Prin) → Decidable (p ≡ q)) where

   data Type : Set where
      ⊤ : Type
      atom : (Q : String) → Type
      _⊃_ : (A B : Type) → Type
      _∧_ : (A B : Type) → Type
      □ : (p : Prin) (A : Type) → Type
      ■ : (p : Prin) (A : Type) → Type

   open JUDGMENTS Type Prin _≡?_ public
   
   