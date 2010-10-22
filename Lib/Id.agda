{-# OPTIONS --universe-polymorphism #-}

module Lib.Id where

open import Lib.Level

module Id where

  infix 5 _≡_
  infixr 5 _≡≡_
  data _≡_ {l : LevelT} {A : Set l} : A → A → Set l where
    Refl : {a : A} → a ≡ a
  IdT : ∀ {l} {A : Set l} → A → A → Set l
  IdT x y = x ≡ y

  {-# BUILTIN EQUALITY IdT #-}
  {-# BUILTIN REFL Refl #-}

  refl : ∀{l} {A : Set l} {a : A} → a ≡ a
  refl = Refl

  symm : ∀{l} {A : Set l} {a b : A} → a ≡ b → b ≡ a
  symm Refl = refl

  trans : ∀{l} {A : Set l} {a b c : A} → a ≡ b → b ≡ c → a ≡ c
  trans Refl Refl = refl

  _≡≡_ : ∀{l} {A : Set l} {a b c : A} → a ≡ b → b ≡ c → a ≡ c
  Refl ≡≡ Refl = Refl

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

open Id public 
  using (IdT ; Refl ; _≡_ ; refl ; symm ; trans ; _≡≡_ 
         ; resp ; resp1 ; resp2 ; resp3)