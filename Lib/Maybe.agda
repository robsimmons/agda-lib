{-# OPTIONS --universe-polymorphism #-}

module Lib.Maybe where

open import Lib.Level
open import Lib.Sum
open import Lib.Product
open import Lib.Imp
open import Lib.Bool
open import Lib.Id

module MAYBE where

   data Maybe {a} (A : Set a) : Set a where
     Just : (x : A) → Maybe A
     Nothing : Maybe A

   return : ∀{a} {A : Set a} → A → Maybe A
   return = Just

   fail : ∀{a} {A : Set a} → Maybe A
   fail = Nothing

   to-poly : ∀{a} {A : Set a} → Maybe A → A + Unit
   to-poly (Just x) = Inl x
   to-poly Nothing = Inr <>

   from-poly : ∀{a} {A : Set a} → A + Unit → Maybe A
   from-poly (Inl x) = Just x
   from-poly (Inr <>) = Nothing

   map : ∀{a b} {A : Set a} {B : Set b} → (A → B) → Maybe A → Maybe B
   map f (Just x) = Just (f x)
   map f Nothing = Nothing 

   isSome : ∀{a} {A : Set a} → Maybe A → Bool
   isSome (Just _) = True
   isSome Nothing = False

   bind : ∀{a} {A B : Set a} → Maybe A → (A → Maybe B) → Maybe B
   bind (Just x) f = f x
   bind Nothing f = fail
   
   valOf : ∀{a} {A : Set a} (s : Maybe A) → {_ : Check (isSome s)} → A
   valOf (Just x) = x
   valOf Nothing {()} 

   valOf-cong : ∀{a} {A : Set a} {a b : Maybe A} 
      → a ≡ b → (chka : Check (isSome a)) (chkb : Check (isSome b))
      → valOf a {chka} ≡ valOf b {chkb}
   valOf-cong {b = Just b} Refl <> <> = refl
   valOf-cong {b = Nothing} Refl () ()

   check-bind : ∀{a} {A B : Set a} {x : Maybe A} {y : A} 
      → (c : Check (isSome x))
      → valOf x {c} ≡ y
      → (f : A → Maybe B)
      → bind x f ≡ f y
   check-bind {x = Just x} <> Refl _ = refl
   check-bind {x = Nothing} () _ _

open MAYBE public
   using (Maybe ; valOf ; isSome ; Nothing ; Just)