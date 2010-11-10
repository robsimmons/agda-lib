{-# OPTIONS --universe-polymorphism #-}

module Lib.Maybe where

open import Lib.Level
open import Lib.Sum
open import Lib.Imp
open import Lib.Bool

module MAYBE where

   Maybe : ∀{a} → Set a → Set a
   Maybe A = A + Void

   map : ∀{a b} {A : Set a} {B : Set b} → (A → B) → Maybe A → Maybe B
   map f = [ f , (λ x → abort x) ]

   isSome : ∀{a} {A : Set a} → Maybe A → Bool
   isSome (Inl _) = True
   isSome (Inr _) = False

   valOf : ∀{a} {A : Set a} (s : Maybe A) → {_ : Check (isSome s)} → A
   valOf (Inl inl) = inl
   valOf (Inr inr) {()} 

open MAYBE public
   using (Maybe)