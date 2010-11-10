{-# OPTIONS --universe-polymorphism #-}

module Lib.Maybe where

open import Lib.Level
open import Lib.Sum
open import Lib.Product
open import Lib.Imp
open import Lib.Bool
open import Lib.Id

module MAYBE where

   Maybe : ∀{a} → Set a → Set a
   Maybe A = A + Unit

   map : ∀{a b} {A : Set a} {B : Set b} → (A → B) → Maybe A → Maybe B
   map f = [ f , const <> ]

   isSome : ∀{a} {A : Set a} → Maybe A → Bool
   isSome (Inl _) = True
   isSome (Inr <>) = False

   return : ∀{a} {A : Set a} → A → Maybe A
   return = Inl

   bind : ∀{a} {A B : Set a} → Maybe A → (A → Maybe B) → Maybe B
   bind (Inl x) f = f x
   bind (Inr <>) f = Inr <>
   
   fail : ∀{a} {A : Set a} → Maybe A
   fail = Inr <>

   valOf : ∀{a} {A : Set a} (s : Maybe A) → {_ : Check (isSome s)} → A
   valOf (Inl inl) = inl
   valOf (Inr inr) {()} 

   valOf-cong : ∀{a} {A : Set a} {a b : Maybe A} 
      → a ≡ b → (chka : Check (isSome a)) (chkb : Check (isSome b))
      → valOf a {chka} ≡ valOf b {chkb}
   valOf-cong {b = Inl b} Refl <> <> = refl
   valOf-cong {b = Inr <>} Refl () ()

   check-bind : ∀{a} {A B : Set a} {x : Maybe A} {y : A} 
      → (c : Check (isSome x))
      → valOf x {c} ≡ y
      → (f : A → Maybe B)
      → bind x f ≡ f y
   check-bind {x = Inl x} <> Refl _ = refl
   check-bind {x = Inr <>} () _ _

open MAYBE public
   using (Maybe ; valOf)