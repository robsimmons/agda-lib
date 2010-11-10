-- Lib.Membership isn't opened directly, but can be "stamped out" for 
-- structures like lists and trees. 
 
{-# OPTIONS --universe-polymorphism #-}

open import Lib.Level
open import Lib.Product
open import Lib.Imp
open import Lib.Maybe
open import Lib.Id using (_≡_)

module Lib.Membership 
  (Collection : ∀{a} → Set a → Set a
   ; Member : ∀{a} {A : Set a} → A → Collection A → Set a) where




module SET where

   Sub : ∀{a} {A : Set a} → Collection A → Collection A → Set a
   Sub xs ys = ∀{x} → Member x xs → Member x ys

   Eq : ∀{a} {A : Set a} → Collection A → Collection A → Set a
   Eq xs ys = Sub xs ys × Sub ys xs

   refl : ∀{a} {A : Set a} {xs : Collection A} → Eq xs xs 
   refl = (λ x' → x') , (λ x' → x')

   symm : ∀{a} {A : Set a} {xs ys : Collection A} → Eq xs ys → Eq ys xs
   symm (f , g) = (λ x' → g x') , (λ x' → f x') 

   trans : ∀{a} {A : Set a} {xs ys zs : Collection A} 
      → Eq xs ys 
      → Eq ys zs
      → Eq xs zs
   trans (f1 , g1) (f2 , g2) = (λ x' → f2 (f1 x')) , (λ x' → g1 (g2 x'))

module BAG where

   Sub : ∀{a} {A : Set a} → Collection A → Collection A → Set a
   Sub xs ys =
      Σ[ f :: (∀{x} → Member x xs → Member x ys) ]
      Σ[ g :: (∀{x} → Member x xs → Maybe (Member x ys)) ]
      ⊤

{-
   Eq : ∀{a} {A : Set a} → Collection A → Collection A → Set a
   Eq xs ys = 
      Σ[ f :: Sub xs ys ] 
      Σ[ g :: Sub ys xs ] 
      (∀{x} (n : Member x xs) → g (f n) ≡ n) ×
      (∀{x} (n : Member x ys) → f (g n) ≡ n)

   toSet : ∀{a} {A : Set a} {xs ys : Collection A} → Eq xs ys → SET.Eq xs ys
   toSet (f , g , _) = (λ x' → f x') , (λ x' → g x')
-}

Some : ∀{a b} {A : Set a}
   → (P : A → Set b) 
   → Collection A  
   → Set (LEVEL.max a b)
Some P xs = ∃ λ x → Member x xs × P x

All : ∀{a b} {A : Set a} 
   → (P : A → Set b) 
   → Collection A 
   → Set (LEVEL.max a b)
All P xs = ∀{x} → Member x xs → P x

