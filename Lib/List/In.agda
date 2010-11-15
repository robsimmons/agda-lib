{-# OPTIONS --universe-polymorphism #-}

module Lib.List.In where 

open import Lib.Id
open import Lib.Product
open import Lib.Sum
open import Lib.Imp
open import Lib.Membership
open import Lib.List.Core 

infixr 4 _∈_

data _∈_ {a} {A : Set a} : A → List A → Set a where
  Z : ∀{x xs} → x ∈ x :: xs 
  S : ∀{x y xs} (n : x ∈ xs) → x ∈ y :: xs
In : ∀{a} {A : Set a} → A → List A → Set a
In x xs = x ∈ xs

in-append : ∀{a} {A : Set a} 
   → {a : A} {as : List A} → a ∈ as
   → (bs : List A)
   → a ∈ as ++ bs
in-append Z bs = Z
in-append (S n) bs = S (in-append n bs)

append-in : ∀{a} {A : Set a}
   → (as : List A)
   → {b : A} {bs : List A} → b ∈ bs
   → b ∈ as ++ bs
append-in [] n = n
append-in (a :: as) n = S (append-in as n)

split-cons : ∀{a} {A : Set a} {x y : A} {ys : List A} 
   → x ∈ (y :: ys) 
   → (x ≡ y) + (x ∈ ys)
split-cons Z = Inl refl
split-cons (S n) = Inr n

case-cons : ∀{a b} {A : Set a} {x y : A} {ys : List A} 
   → (P : A → Set b)
   → P y
   → (∀{y} → y ∈ ys → P y)
   → x ∈ y :: ys
   → P x
case-cons P ez es Z = ez
case-cons P ez es (S n) = es n

split-append : ∀{a} {A : Set a} {x : A} {xs ys : List A} 
   → x ∈ (xs ++ ys)
   → (x ∈ xs) + (x ∈ ys)
split-append {xs = []} n = Inr n
split-append {xs = x :: xs} Z = Inl Z
split-append {xs = x :: xs} (S n) = case (split-append n) (Inl o S) Inr

module SET where
   open MEMBERSHIP.SET List In public
   
   sub-cons : ∀{a} {A : Set a} {x : A} {xs : List A} → Sub xs (x :: xs)
   sub-cons = S

   sub-wken : ∀{a} {A : Set a} {x : A} {xs : List A} → Sub xs (x :: xs)
   sub-wken = S

   sub-exch : ∀{a} {A : Set a} {x y : A} {xs : List A} 
       → Sub (x :: y :: xs) (y :: x :: xs)
   sub-exch Z = S Z
   sub-exch (S Z) = Z
   sub-exch (S (S n)) = S (S n)

   sub-wkex : ∀{a} {A : Set a} {x y : A} {xs : List A} 
       → Sub (x :: xs) (x :: y :: xs)
   sub-wkex Z = Z
   sub-wkex (S n) = S (S n)

   sub-cntr : ∀{a} {A : Set a} {x : A} {xs : List A} 
       → Sub (x :: x :: xs) (x :: xs)
   sub-cntr Z = Z
   sub-cntr (S Z) = Z
   sub-cntr (S (S n)) = S n

   sub-appendr : ∀{a} {A : Set a} 
      → (xs : List A)
      → (ys : List A)
      → Sub xs (xs ++ ys)
   sub-appendr [] ys ()
   sub-appendr (x' :: xs) ys Z = Z
   sub-appendr (x' :: xs) ys (S n) = S (sub-appendr xs ys n)

   sub-appendl : ∀{a} {A : Set a} 
      → (xs : List A)
      → (ys : List A)
      → Sub xs (ys ++ xs)
   sub-appendl xs [] n = n
   sub-appendl xs (y :: ys) n = S (sub-appendl xs ys n)

   sub-cons-cong : ∀{a} {A : Set a} {x y : A} {xs ys : List A} 
      → x ≡ y
      → Sub xs ys
      → Sub (x :: xs) (y :: ys)
   sub-cons-cong Refl f Z = Z
   sub-cons-cong Refl f (S n) = S (f n)

   sub-cons-congr : ∀{a} {A : Set a} {x : A} {xs ys : List A} 
      → Sub xs ys
      → Sub (x :: xs) (x :: ys)
   sub-cons-congr = sub-cons-cong ID.refl

{-
   sub-appendl : ∀{a} {A : Set a} {x y : A} {ys1 ys2 : List A}
      → (xs : List A)
      → Sub ys1 ys2 
      → Sub (xs ++ ys1) (xs ++ ys2)
   sub-appendl xs f = {!!}
-}

   cons-cong : ∀{a} {A : Set a} {x y : A} {xs ys : List A} 
      → x ≡ y
      → Eq xs ys
      → Eq (x :: xs) (y :: ys)
   cons-cong Refl (f , g) = 
      (λ n → sub-cons-cong ID.refl f n) , (λ n → sub-cons-cong ID.refl g n)

module BAG where
   open MEMBERSHIP.BAG List In public

module ANY where
   open MEMBERSHIP.ANY List In public

module ALL where
   open MEMBERSHIP.ALL List In public

open MEMBERSHIP List In public using (Any ; All)