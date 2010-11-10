{- Following the general pattern, some rules for dealing with polynomial data 
types and implication. Hopefully I won't reget exporting all of these directly
into the top-level... -}

{-# OPTIONS --universe-polymorphism #-}

module Lib.Imp where
 
open import Lib.Level
open import Lib.Product
open import Lib.Sum
open import Lib.Not
  
module IMP where

   Imp : ∀{a b} (A : Set a) (B : Set b) → Set (LEVEL.max a b)
   Imp A B = A → B

   const : ∀{a b} {A : Set a} {B : Set b} → A → B → A
   const x y = x

   id : ∀{a} (A : Set a) → A → A
   id A x = x

   _o_ : ∀{a b c} {A : Set a} {B : Set b} {C : Set c}
      → Imp B C 
      → Imp A B
      → Imp A C
   f o g = λ x → f (g x)

   neg-or : ∀{a} {A B : Set a} → ¬ (A + B) → ¬ A × ¬ B
   neg-or f = (λ x → f (Inl x)) , (λ y → f (Inr y))

   neg-and-neg : ∀{a} {A B : Set a} → ¬ A × ¬ B → ¬ (A + B)
   neg-and-neg (f , g) (Inl x) = f x
   neg-and-neg (f , g) (Inr x) = g x

   neg-and : ∀{a} {A B : Set a} → Decidable A → Decidable B → 
      ¬ (A × B) → ¬ A + ¬ B
   neg-and (Inr x) _ f = Inl x 
   neg-and (Inl x) (Inr y) f = Inr y
   neg-and (Inl x) (Inl y) f = abort (f (x , y))

   neg-or-neg : ∀{a} {A B : Set a} → ¬ A + ¬ B → ¬ (A × B)
   neg-or-neg (Inl f) p = f (fst p)
   neg-or-neg (Inr g) p = g (snd p)

   or-cong : ∀{a} {A B C D : Set a} → (A → B) → (C → D) → (A + C → B + D)
   or-cong f g (Inl x) = Inl (f x)
   or-cong f g (Inr x) = Inr (g x)

   or-congl : ∀{a} {A B C : Set a} → (A → B) → (A + C → B + C)
   or-congl f (Inl x) = Inl (f x)
   or-congl f (Inr x) = Inr x

   or-congr : ∀{a} {A B C : Set a} → (A → B) → (C + A → C + B)
   or-congr g (Inl x) = Inl x
   or-congr g (Inr x) = Inr (g x)

   not-cong : ∀{a} {A B : Set a} → (A → B) → ¬ B → ¬ A
   not-cong f b a = b (f a)

   and-cong : ∀{a} {A B C D : Set a} → (A → B) → (C → D) → (A × C → B × D)
   and-cong f g (x , y) = (f x , g y)

   and-congl : ∀{a} {A B C : Set a} → (A → B) → (A × C → B × C)
   and-congl f (x , y) = (f x , y)

   and-congr : ∀{a} {A B C : Set a} → (A → B) → (C × A → C × B)
   and-congr g (x , y) = (x , g y)

open IMP public