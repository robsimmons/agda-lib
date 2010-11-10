{-# OPTIONS --universe-polymorphism #-}

module Lib.Sum where 

open import Lib.Level
open import Lib.Product

module SUM where

   data Void {l : Level} : Set l where
   ⊥ = Void {Z}
   Void0 = Void {Z}

   abort : ∀{a b} {A : Set a} → Void {b} → A
   abort ()

   data _+_ {l : Level} (A : Set l) (B : Set l) : Set l where
      Inl : (inl : A) → A + B
      Inr : (inr : B) → A + B
   Sum : ∀ {l} (A : Set l) (B : Set l) → Set l
   Sum A B = A + B
   Sum0 = Sum {Z}

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
     (⊥ ; Void ; Void0 ; abort ; Inl ; Inr ; Sum ; Sum0 ; _+_ ; case ; [_,_]) 
