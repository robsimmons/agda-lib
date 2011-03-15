------------------------------------------------------------------------
-- Basic types related to coinduction
------------------------------------------------------------------------

{-# OPTIONS --universe-polymorphism #-}

module Lib.Coinduction where

open import Lib.Level

module COINDUCTION where
 
   postulate
      Lazy : ∀{a} (A : Set a) → Set a
      thunk : ∀{a} {A : Set a} → A → Lazy A
      force : ∀{a} {A : Set a} → Lazy A → A

   {-# BUILTIN INFINITY Lazy  #-}
   {-# BUILTIN SHARP    thunk #-}
   {-# BUILTIN FLAT     force #-}

open COINDUCTION public
   using (Lazy ; thunk ; force)


