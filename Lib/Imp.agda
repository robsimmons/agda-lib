{- Following the general pattern, some rules for dealing with polynomial data 
types and implication. Hopefully I won't reget exporting all of these directly
into the top-level... -}

{-# OPTIONS --universe-polymorphism #-}

module Lib.Imp where
 
open import Lib.Product
open import Lib.Sum
open import Lib.Not
  
module Imp where

Imp : ∀{a} (A B : Set a) → Set a
Imp A B = A → B

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

or-cong1 : ∀{a} {A B C : Set a} → (A → B) → (A + C → B + C)
or-cong1 f (Inl x) = Inl (f x)
or-cong1 f (Inr x) = Inr x

or-cong2 : ∀{a} {A B C : Set a} → (A → B) → (C + A → C + B)
or-cong2 g (Inl x) = Inl x
or-cong2 g (Inr x) = Inr (g x)

not-cong : ∀{a} {A B : Set a} → (A → B) → ¬ B → ¬ A
not-cong f b a = b (f a)

and-cong : ∀{a} {A B C D : Set a} → (A → B) → (C → D) → (A × C → B × D)
and-cong f g (x , y) = (f x , g y)

and-cong1 : ∀{a} {A B C : Set a} → (A → B) → (A × C → B × C)
and-cong1 f (x , y) = (f x , y)

and-cong2 : ∀{a} {A B C : Set a} → (A → B) → (C × A → C × B)
and-cong2 g (x , y) = (x , g y)

