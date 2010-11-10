-- Lib.Membership isn't opened directly, but can be "stamped out" for 
-- structures like lists and trees. 
 
{-# OPTIONS --universe-polymorphism #-}

open import Lib.Level
open import Lib.Product
open import Lib.Imp
open import Lib.Maybe
open import Lib.Bool
open import Lib.Id using (_≡_ ; _≡≡_ ; resp)

module Lib.Membership where

module MEMBERSHIP 
  (Collection : ∀{a} → Set a → Set a
   ; Member : ∀{a} {A : Set a} → A → Collection A → Set a) where

   module SET where

      Sub : ∀{a} {A : Set a} → Collection A → Collection A → Set a
      Sub xs ys = ∀{x} → Member x xs → Member x ys

      refl-sub : ∀{a} {A : Set a} {xs : Collection A} → Sub xs xs
      refl-sub n = n

      trans-sub : ∀{a} {A : Set a} {xs ys zs : Collection A}
         → Sub xs ys 
         → Sub ys zs
         → Sub xs zs
      trans-sub f g = g o f    

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

      trans-sub-eq : ∀{a} {A : Set a} {xs ys zs : Collection A} 
         → Sub xs ys 
         → Eq ys zs
         → Sub xs zs
      trans-sub-eq f1 (f2 , g2) = trans-sub f1 f2

      trans-eq-sub : ∀{a} {A : Set a} {xs ys zs : Collection A} 
         → Eq xs ys 
         → Sub ys zs
         → Sub xs zs
      trans-eq-sub (f1 , g1) f2 = trans-sub f1 f2

   module BAG where

      Sub : ∀{a} {A : Set a} → Collection A → Collection A → Set a
      Sub xs ys =
         Σ[ f :: (∀{x} → Member x xs → Member x ys) ]
         Σ[ g :: (∀{x} → Member x ys → Maybe (Member x xs)) ]
         (∀{x} (n : Member x xs) → ∃ λ c → valOf (g (f n)) {c} ≡ n)

      refl-sub : ∀{a} {A : Set a} {xs : Collection A} → Sub xs xs
      refl-sub = (λ n → n) , (λ n → MAYBE.return n) , (λ n → <> , Lib.Id.refl)

      trans-sub : ∀{a} {A : Set a} {xs ys zs : Collection A}
         → Sub xs ys 
         → Sub ys zs
         → Sub xs zs
      trans-sub (f1 , g1 , inj1) (f2 , g2 , inj2) = 
         (λ n → f2 (f1 n))
         , (λ n → MAYBE.bind (g2 n) g1)
         , (λ n → 
            Lib.Id.coe
             (Lib.Id.symm
              (resp (λ n' → Check (MAYBE.isSome n'))
               (MAYBE.check-bind (fst (inj2 (f1 n))) (snd (inj2 (f1 n)))
                (λ n' → g1 n'))))
             (fst (inj1 n))
            , MAYBE.valOf-cong
                (MAYBE.check-bind (fst (inj2 (f1 n))) (snd (inj2 (f1 n)))
                 (λ n' → g1 n'))
                (Lib.Id.coe
                   (Lib.Id.symm
                    (resp (λ n' → Check (MAYBE.isSome n'))
                     (MAYBE.check-bind (fst (inj2 (f1 n))) (snd (inj2 (f1 n)))
                      (λ n' → g1 n'))))
                   (fst (inj1 n))) (fst (inj1 n)) 
              ≡≡ snd (inj1 n))

   module ANY where

      Any : ∀{a b} {A : Set a}
         → (P : A → Set b) 
         → Collection A  
         → Set (LEVEL.max a b)
      Any P xs = ∃ λ x → Member x xs × P x

   open ANY public using (Any)

   module ALL where

      All : ∀{a b} {A : Set a} 
         → (P : A → Set b) 
         → Collection A 
         → Set (LEVEL.max a b)
      All P xs = ∀{x} → Member x xs → P x

      pull :  ∀{a} {A : Set a} {x : A} {xs : Collection A} {P : A → Set a} 
         → Member x xs 
         → All P xs 
         → P x
      pull n c = c n

   open ALL public using (All)