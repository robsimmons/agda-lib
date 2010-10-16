-- Accessibility relations on natural numbers
-- Robert J. Simmons

open import Compat
open import Accessibility.Inductive
import Accessibility.SuccStar

module Accessibility.Nat where

  _≺_ : Nat → Nat → Set
  (S n) ≺ m = m ≡ n
  Z ≺ m = Void
  _≡?_ : (w : Nat) (w' : Nat) → Decidable (w ≡ w')
  Z ≡? Z = inj₁ refl
  Z ≡? (S m) = inj₂ (λ ())
  (S n) ≡? Z = inj₂ (λ ())
  (S n) ≡? (S m) with n ≡? m
  (S n) ≡? (S .n) | inj₁ refl = inj₁ refl
  (S n) ≡? (S m) | inj₂ neq = inj₂ (λ x → neq (injS x))

  unique : ∀{m n n'} → m ≺ n → m ≺ n' → n ≡ n'
  unique {Z} s1 s2 = abort s1
  unique {S y} s1 s2 = trans s1 (sym s2)
    
  mutual 
    call : (P : Nat → Set) 
       → ((n : Nat) → ((m : Nat) → n ≺ m → P m) → P n)
       → ((m n : Nat) → n ≡ m → P n)
    call P iH .n n refl = ind P iH n

    ind : (P : Nat → Set) 
       → ((n : Nat) → ((m : Nat) → n ≺ m → P m) → P n)
       → ((n : Nat) → P n)
    ind P iH Z = iH Z (λ m ())
    ind P iH (S n) = iH (S n) (call P iH n)


  

  Count : UpwardsWellFounded
  Count = 
    record {W = Nat;
            _≺_ = _≺_;
            _≡?_ = _≡?_;
            ind = ind}

  module Greater* = Accessibility.SuccStar Count
 
  Geq : UpwardsWellFounded
  Geq = 
    record {W = Nat;
            _≺_ = Greater*._≺+_;
            _≡?_ = _≡?_;
            ind = Greater*.ind+}

