------------------------------------------------------------------------
-- Basic types related to coinduction
------------------------------------------------------------------------

{-# OPTIONS --universe-polymorphism #-}

module Lib.Coinduction where

open import Lib.Level

module COINDUCTION where

   infix 1000 susp_
 
   postulate
      Inf : ∀{a} (A : Set a) → Set a
      susp_ : ∀{a} {A : Set a} → A → Inf A
      force : ∀{a} {A : Set a} → Inf A → A

   {-# BUILTIN INFINITY Inf  #-}
   {-# BUILTIN SHARP    susp_ #-}
   {-# BUILTIN FLAT     force #-}

open COINDUCTION public
   using (Inf ; susp_ ; force)


