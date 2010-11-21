{-# OPTIONS --universe-polymorphism #-}

module Lib.Sum where 

open import Lib.Level
open import Lib.Product

module SUM where

   data Void : Set where
   ⊥ = Void

   abort : ∀{a} {A : Set a} → Void → A
   abort ()

   data _+_ {a b} (A : Set a) (B : Set b) : Set (LEVEL.max a b) where
      Inl : (inl : A) → A + B
      Inr : (inr : B) → A + B
   Sum : ∀{a b} (A : Set a) (B : Set b) → Set (LEVEL.max a b)
   Sum A B = A + B
   Sum0 = Sum {Z} {Z}

   case : ∀{a b} {A B : Set a} {C : Set b} → A + B → (A → C) → (B → C) → C
   case (Inl x) f g = f x
   case (Inr x) f g = g x 

   map : ∀{a b} {A B : Set a} {C D : Set b} → (A → C) → (B → D) → A + B → C + D
   map f g (Inl x) = Inl (f x)
   map f g (Inr x) = Inr (g x)
 
   [_,_] : ∀{a b} {A B : Set a} {C D : Set b} 
      → (A → C) 
      → (B → D)
      → (A + B → C + D)
   [ f , g ] = map f g

open SUM public
   using
     (⊥ ; Void ; abort ; Inl ; Inr ; Sum ; Sum0 ; _+_ ; case ; [_,_]) 
