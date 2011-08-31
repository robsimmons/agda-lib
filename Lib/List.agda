{-# OPTIONS --universe-polymorphism #-}

module Lib.List where

open import Lib.Id
open import Lib.Product
open import Lib.Sum

module LIST where
   open import Lib.List.Core public
   open import Lib.List.In public
  
   cons-cong : ∀{a} {A : Set a} {a b : A} {as bs : List A} 
      → a ≡ b 
      → as ≡ bs 
      → (a :: as) ≡ (b :: bs)
   cons-cong Refl Refl = refl

   cons-congl : ∀{a} {A : Set a} {a b : A} {as : List A} 
      → a ≡ b 
      → (a :: as) ≡ (b :: as)
   cons-congl Refl = refl

   cons-congr : ∀{a} {A : Set a} {a : A} {as bs : List A} 
      → as ≡ bs 
      → (a :: as) ≡ (a :: bs)
   cons-congr Refl = refl

   cons-elim : ∀{a} {A : Set a} {a b : A} {as bs : List A} 
      → (a :: as) ≡ (b :: bs)
      → (a ≡ b) × (as ≡ bs)
   cons-elim Refl = refl , refl

   append-nil : ∀{a} {A : Set a} {as : List A} → as ++ [] ≡ as
   append-nil {as = []} = refl
   append-nil {as = a :: as} = cons-congr (append-nil {as = as})

   assoc-append : ∀{a} {A : Set a} {as bs cs : List A}
      → (as ++ (bs ++ cs)) ≡ ((as ++ bs) ++ cs)
   assoc-append {as = []} = refl
   assoc-append {as = a :: as} = cons-congr (assoc-append {as = as})

   append-assoc : ∀{a} {A : Set a} {as bs cs : List A}
      → ((as ++ bs) ++ cs) ≡ (as ++ (bs ++ cs)) 
   append-assoc {as = []} = refl
   append-assoc {as = a :: as} = cons-congr (append-assoc {as = as})
     
   map : ∀{a} {A B : Set a} → (A → B) → List A → List B
   map f [] = []
   map f (x :: xs) = f x :: map f xs

   in-map : ∀{a} {A B : Set a} {a : A} {as : List A} 
      → (f : A → B)
      → a ∈ as 
      → f a ∈ map f as
   in-map f Z = Z
   in-map f (S n) = S (in-map f n)

   cross : ∀{a} {A B C : Set a} → (A → B → C) → List A → List B → List C
   cross f [] bs = []
   cross f (a :: as) bs = map (f a) bs ++ cross f as bs
  
   concat : ∀{a} {A B : Set a} → (A → List B) → List A → List B
   concat f [] = []
   concat f (a :: as) = f a ++ concat f as

   in-concat : ∀{a} {A B : Set a} {a : A} {b : B} {as : List A}
      (f : A → List B) → a ∈ as → b ∈ f a → b ∈ concat f as
   in-concat f Z y = in-append y _
   in-concat f (S n) y = append-in (f _) (in-concat f n y)

open LIST public
  using (List ; [] ; [_] ; _::_ ; _++_ ; _∈_ ; Z ; S)
