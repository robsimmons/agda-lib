{-# OPTIONS --universe-polymorphism #-}

module Lib.Id where

open import Lib.Level

module ID where

   infix 5 _≡_
   infixr 5 _≡≡_
   data _≡_ {l : Level} {A : Set l} : A → A → Set l where
      Refl : {a : A} → a ≡ a
   Id : ∀ {l} {A : Set l} → A → A → Set l
   Id x y = x ≡ y

   {-# BUILTIN EQUALITY Id #-}
   {-# BUILTIN REFL Refl #-}

   refl : ∀{a} {A : Set a} {a : A} → a ≡ a
   refl = Refl

   symm : ∀{a} {A : Set a} {a b : A} → a ≡ b → b ≡ a
   symm Refl = refl

   trans : ∀{a} {A : Set a} {a b c : A} → a ≡ b → b ≡ c → a ≡ c
   trans Refl Refl = refl

   _≡≡_ : ∀{a} {A : Set a} {a b c : A} → a ≡ b → b ≡ c → a ≡ c
   Refl ≡≡ Refl = Refl

   coe : ∀{a} {A : Set a} {B : Set a} -> A ≡ B -> A -> B
   coe Refl x = x

   resp : ∀{a b} {A : Set a} {B : Set b} (p : A → B) → {a1 a2 : A} 
      → a1 ≡ a2 
      → p a1 ≡ p a2
   resp _ Refl = refl

   resp1 : ∀{a b} {A : Set a} {B : Set b} (p : A → B) → {a1 a2 : A} 
      → a1 ≡ a2 
      → p a1 ≡ p a2
   resp1 _ Refl = refl

   resp2 : ∀{a b c} {A : Set a} {B : Set b} {C : Set c} 
      → (p : A → B → C) → {a1 a2 : A} {b1 b2 : B} 
      → a1 ≡ a2 
      → b1 ≡ b2 
      → p a1 b1 ≡ p a2 b2
   resp2 _ Refl Refl = refl

   resp3 : ∀{a b c d} {A : Set a} {B : Set b} {C : Set c} {D : Set d}
      → (p : A → B → C → D) → {a1 a2 : A} {b1 b2 : B} {c1 c2 : C} 
      → a1 ≡ a2 
      → b1 ≡ b2 
      → c1 ≡ c2 
      → p a1 b1 c1 ≡ p a2 b2 c2
   resp3 _ Refl Refl Refl = refl

open ID public 
   using 
     (Id ; Refl ; _≡_ ; refl ; symm ; trans ; _≡≡_ ; 
      coe ; resp ; resp1 ; resp2 ; resp3)