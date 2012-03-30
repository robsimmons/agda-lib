
open import Prelude
open import UnifiedCtx

module Unified where

data Type : Polarity -> Set where
  a : (Q : String) {⁼ : Polarity} → Type ⁼
  ↑ : (A : Type ⁺) → Type ⁻
  ↓ : (A : Type ⁺) → Type ⁻
  _&_ : (A B : Type ⁻) → Type ⁻
  _⊕_ : (A B : Type ⁺) → Type ⁻

module LOGIC (UC : UCtx Type) where
  open UCtx UC public
 
  data RFocus (N : Nat) : Ctx N → Type ⁺ → Set where
     
     ⊕L₁ : 