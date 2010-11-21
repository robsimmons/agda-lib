{-# OPTIONS --universe-polymorphism #-}

module Lib.Product where 

open import Lib.Level
open import Lib.Id

module PRODUCT where

   infixr 0 _,_
   infix 0 ,_
   infixr 10 _×_

   record Unit : Set where
      constructor <> 
   ⊤ = Unit
  
   {- This is not yet a record, because you can't pattern match records -}
   record Σ {a b} (A : Set a) (B : A → Set b) : Set (LEVEL.max a b) where
      constructor _,_
      field
         fst : A 
         snd : B fst
   open Σ public

   Product : ∀{a b} (A : Set a) (B : A → Set b) → Set (LEVEL.max a b)
   Product A B = Σ A B
   Product0 = Product {Z} {Z}

   syntax Σ A (λ x → B) = Σ[ x :: A ] B
 
   ∃ : ∀{a b} {A : Set a} → (A → Set b) → Set (LEVEL.max a b)
   ∃ = Σ _

   _×_ : ∀{a b} (A : Set a) (B : Set b) → Set (LEVEL.max a b)
   A × B = Σ[ x :: A ] B

   ,_ : ∀{a b} {A : Set a} {B : A → Set b} {x} → B x → ∃ B
   , snd = _ , snd

   pair-cong : ∀{a b} {A : Set a} {B : Set b} {x1 x2 : A} {y1 y2 : B}
      → x1 ≡ x2 
      → y1 ≡ y2 
      → (x1 , y1) ≡ (x2 , y2)
   pair-cong Refl Refl = Refl

   pair-cong1 : ∀{a b} {A : Set a} {B : Set b} {x1 x2 : A} {y : B}
      → x1 ≡ x2 
      → (x1 , y) ≡ (x2 , y)
   pair-cong1 Refl = Refl

   pair-cong2 : ∀{a b} {A : Set a} {B : Set b} {x : A} {y1 y2 : B}
      → y1 ≡ y2 
      → (x , y1) ≡ (x , y2)
   pair-cong2 Refl = Refl

open PRODUCT public
   using 
     (⊤ ; Unit ; <> ; Σ ; _,_ ; fst ; snd ; ∃ ; _×_ ; ,_ ; Product)
