-- "Countdown" accessibility relations on natural numbers
-- Robert J. Simmons

module Accessibility.Nat where

open import Prelude
open import Accessibility.Inductive

_≺_ : Nat → Nat → Set
(S n) ≺ m = m ≡ n
Z ≺ m = ⊥

_≡?_ : (w : Nat) (w' : Nat) → Decidable (w ≡ w')
Z ≡? Z = Inl refl
Z ≡? (S m) = Inr (λ ())
(S n) ≡? Z = Inr (λ ())
(S n) ≡? (S m) with n ≡? m
(S n) ≡? (S .n) | Inl Refl = Inl refl
(S n) ≡? (S m) | Inr neq = Inr (λ x → neq (NAT.s-elim x))

unique : ∀{m n n'} → m ≺ n → m ≺ n' → n ≡ n'
unique {Z} s1 s2 = abort s1
unique {S y} s1 s2 = trans s1 (symm s2)
    
mutual 
   call : (P : Nat → Set) 
      → ((n : Nat) → ((m : Nat) → n ≺ m → P m) → P n)
      → ((m n : Nat) → n ≡ m → P n)
   call P iH .n n Refl = ind P iH n

   ind : (P : Nat → Set) 
      → ((n : Nat) → ((m : Nat) → n ≺ m → P m) → P n)
      → ((n : Nat) → P n)
   ind P iH Z = iH Z (λ m ())
   ind P iH (S n) = iH (S n) (call P iH n)

Count : UpwardsWellFounded
Count = record
  {W = Nat
   ; _≺_ = _≺_
   ; _≡?_ = _≡?_
   ; ind = ind}
 
Geq : UpwardsWellFounded
Geq = TRANS-UWF.TransUWF Count


