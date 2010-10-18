-- Accessibility relations on natural numbers
-- Robert J. Simmons

open import Prelude
open import CPL.Accessibility.Inductive
import CPL.Accessibility.SuccStar

module CPL.Accessibility.Nat where

  _≺_ : NatT → NatT → Set
  (S n) ≺ m = m ≡ n
  Z ≺ m = ⊥
  _≡?_ : (w : NatT) (w' : NatT) → Decidable (w ≡ w')
  Z ≡? Z = Inl refl
  Z ≡? (S m) = Inr (λ ())
  (S n) ≡? Z = Inr (λ ())
  (S n) ≡? (S m) with n ≡? m
  (S n) ≡? (S .n) | Inl Refl = Inl refl
  (S n) ≡? (S m) | Inr neq = Inr (λ x → neq (Nat.succ-elim x))

  unique : ∀{m n n'} → m ≺ n → m ≺ n' → n ≡ n'
  unique {Z} s1 s2 = abort s1
  unique {S y} s1 s2 = trans s1 (symm s2)
    
  mutual 
    call : (P : NatT → Set) 
       → ((n : NatT) → ((m : NatT) → n ≺ m → P m) → P n)
       → ((m n : NatT) → n ≡ m → P n)
    call P iH .n n Refl = ind P iH n

    ind : (P : NatT → Set) 
       → ((n : NatT) → ((m : NatT) → n ≺ m → P m) → P n)
       → ((n : NatT) → P n)
    ind P iH Z = iH Z (λ m ())
    ind P iH (S n) = iH (S n) (call P iH n)

  Count : UpwardsWellFounded
  Count = 
    record {W = NatT;
            _≺_ = _≺_;
            _≡?_ = _≡?_;
            ind = ind}

  module Greater* = CPL.Accessibility.SuccStar Count
 
  Geq : UpwardsWellFounded
  Geq = 
    record {W = NatT;
            _≺_ = Greater*._≺+_;
            _≡?_ = _≡?_;
            ind = Greater*.ind+}

