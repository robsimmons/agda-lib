{-# OPTIONS --universe-polymorphism #-}

module Lib.Bool where

open import Lib.Level
open import Lib.Product
open import Lib.Sum
open import Lib.Id
open import Lib.Imp

module BOOL where
 
   data Bool : Set where
      True : Bool
      False : Bool
   {-# COMPILED_DATA Bool Bool True False #-}
   {-# BUILTIN BOOL  Bool  #-}
   {-# BUILTIN TRUE  True  #-}
   {-# BUILTIN FALSE False #-}

   if_/_then_else : ∀{a} (P : Bool → Set a) (b : Bool) → P True → P False → P b
   if _ / True then b1 else b2 = b1
   if _ / False then b1 else b2 = b2

   _×b_ : Bool → Bool → Bool
   False ×b False = False
   b ×b True = b
   True ×b b = b

   _+b_ : Bool → Bool → Bool 
   True +b True = True
   False +b b = b
   b +b False = b

   Check : Bool → Set
   Check True = Unit
   Check False = Void

   options : (b : Bool) → (b ≡ True) + (b ≡ False)
   options True = Inl refl
   options False = Inr refl

open BOOL public 
   using (Bool ; True ; False ; if_/_then_else ; _×b_ ; _+b_ ; Check)