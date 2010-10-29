{-# OPTIONS --universe-polymorphism #-}


module Lib.List where 

open import Lib.Id

module List where

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

  append-cong2 : ∀{a} {A : Set a} {a : A} {as bs : List A} 
     → as ≡ bs 
     → (a :: as) ≡ (a :: bs)
  append-cong2 Refl = refl

  append-nil : ∀{a} {A : Set a} {as : List A} → as ++ [] ≡ as
  append-nil {as = []} = refl
  append-nil {as = a :: as} = append-cong2 (append-nil {as = as})

  assoc-append : ∀{a} {A : Set a} {as bs cs : List A}
     → (as ++ (bs ++ cs)) ≡ ((as ++ bs) ++ cs)
  assoc-append {as = []} = refl
  assoc-append {as = a :: as} = append-cong2 (assoc-append {as = as})
  
  map : ∀{a} {A B : Set a} → (A → B) → List A → List B
  map f [] = []
  map f (x :: xs) = f x :: map f xs

open List public
  using ([] ; [_] ; _::_ ; _++_ )
  renaming (List to ListT)

