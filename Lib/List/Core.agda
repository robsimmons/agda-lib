{-# OPTIONS --universe-polymorphism #-}

module Lib.List.Core where 

open import Lib.Id
open import Lib.Product

infixr 5 _::_
infixr 5 _++_
data List {a} (A : Set a) : Set a where
  [] : List A
  _::_ : A → List A → List A

[_] : ∀{a} {A : Set a} → A → List A
[ x ] = x :: []

_++_ : ∀{a} {A : Set a} → List A -> List A -> List A
[] ++ ys = ys
(x :: xs) ++ ys = x :: (xs ++ ys)

cons-cong : ∀{a} {A : Set a} {a b : A} {as bs : List A} 
   → a ≡ b 
   → as ≡ bs 
   → (a :: as) ≡ (b :: bs)
cons-cong Refl Refl = refl

cons-cong1 : ∀{a} {A : Set a} {a b : A} {as : List A} 
   → a ≡ b 
   → (a :: as) ≡ (b :: as)
cons-cong1 Refl = refl

cons-cong2 : ∀{a} {A : Set a} {a : A} {as bs : List A} 
   → as ≡ bs 
   → (a :: as) ≡ (a :: bs)
cons-cong2 Refl = refl

cons-elim : ∀{a} {A : Set a} {a b : A} {as bs : List A} 
   → (a :: as) ≡ (b :: bs)
   → (a ≡ b) × (as ≡ bs)
cons-elim Refl = refl , refl

append-nil : ∀{a} {A : Set a} {as : List A} → as ++ [] ≡ as
append-nil {as = []} = refl
append-nil {as = a :: as} = cons-cong2 (append-nil {as = as})

assoc-append : ∀{a} {A : Set a} {as bs cs : List A}
   → (as ++ (bs ++ cs)) ≡ ((as ++ bs) ++ cs)
assoc-append {as = []} = refl
assoc-append {as = a :: as} = cons-cong2 (assoc-append {as = as})

append-assoc : ∀{a} {A : Set a} {as bs cs : List A}
   → ((as ++ bs) ++ cs) ≡ (as ++ (bs ++ cs)) 
append-assoc {as = []} = refl
append-assoc {as = a :: as} = cons-cong2 (append-assoc {as = as})
  
map : ∀{a} {A B : Set a} → (A → B) → List A → List B
map f [] = []
map f (x :: xs) = f x :: map f xs


