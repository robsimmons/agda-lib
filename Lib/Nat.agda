{-# OPTIONS --universe-polymorphism #-}
-- Most of the theorems proved here (and many that were not) are listed here:
-- www.cs.princeton.edu/~rsimmons/cheatsheet.pdf

module Lib.Nat where

import Lib.Level
open import Lib.Product
open import Lib.Sum
open import Lib.Id

module Nat where

  data Nat : Set where
    Z : Nat
    S : Nat → Nat

  {-# BUILTIN NATURAL Nat #-}
  {-# BUILTIN SUC S #-}
  {-# BUILTIN ZERO Z #-}

  fold : {P : Nat → Set} → 
         P Z → 
         ((n : Nat) → P n → P (S n)) → 
         (n : Nat) → P n
  fold zc sc Z = zc
  fold zc sc (S n) = sc n (fold zc sc n)
     
  _+n_ : Nat → Nat → Nat
  Z +n b = b
  S a +n b = S (a +n b)

  _×n_ : Nat → Nat → Nat
  Z ×n b = Z
  (S a) ×n b = (a ×n b) +n b

  max : Nat → Nat → Nat
  max  Z    b     = b
  max (S a) Z     = S a
  max (S a) (S b) = S (max a b)

  succ-cong : ∀{a b} → a ≡ b → S a ≡ S b
  succ-cong Refl = refl 

  succ-elim : ∀{a b} → S a ≡ S b → a ≡ b
  succ-elim Refl = refl

  {- Addition (simplification) -}

  zero-plus : ∀{a} → 0 +n a ≡ a
  zero-plus = refl

  plus-zero : ∀{a} → a +n 0 ≡ a
  plus-zero {Z} = refl
  plus-zero {S a} = succ-cong (plus-zero {a})

  {- Addition (rearrangement) -}

  succ-plus : ∀{a b} → a +n S b ≡ S a +n b
  succ-plus {Z} = refl
  succ-plus {S a} = succ-cong (succ-plus {a})

  plus-succ : ∀{a b} → S a +n b ≡ a +n S b
  plus-succ {Z} = refl
  plus-succ {S a} = succ-cong (plus-succ {a})

  plus-comm : ∀{a b} → a +n b ≡ b +n a
  plus-comm {Z} = symm plus-zero
  plus-comm {S a}{b} = succ-cong (plus-comm {a}) ≡≡ plus-succ {b} {a}

  comm-plus : ∀{a b} → b +n a ≡ a +n b
  comm-plus {_}{a} = plus-comm {a}

  plus-assoc : ∀{a b c} → (a +n b) +n c ≡ a +n (b +n c)
  plus-assoc {Z} = refl
  plus-assoc {S a} = succ-cong (plus-assoc {a})

  assoc-plus : ∀{a b c} → a +n (b +n c) ≡ (a +n b) +n c
  assoc-plus {Z} = refl
  assoc-plus {S a} = succ-cong (assoc-plus {a})

  {- Addition (equality) -} 

  plus-cong : ∀{a₁ a₂ b₁ b₂} → a₁ ≡ a₂ → b₁ ≡ b₂ → a₁ +n b₁ ≡ a₂ +n b₂
  plus-cong Refl Refl = refl

  plus-cong1 : ∀{a₁ a₂ b} → a₁ ≡ a₂ → a₁ +n b ≡ a₂ +n b
  plus-cong1 Refl = refl

  plus-cong2 : ∀{a b₁ b₂} → b₁ ≡ b₂ → a +n b₁ ≡ a +n b₂
  plus-cong2 Refl = refl

  plus-elim1 : ∀{a b c} → a +n b ≡ a +n c → b ≡ c
  plus-elim1 {Z} Refl = refl
  plus-elim1 {S a} eq with plus-elim1 {a} (succ-elim eq) 
  ... | Refl = refl

  plus-elim2 : ∀{a b c} → a +n c ≡ b +n c → a ≡ b
  plus-elim2 {a}{b}{c} eq =
     plus-elim1 {c}{a}{b} (comm-plus {a}{c} ≡≡ eq ≡≡ comm-plus {c}{b})

  {- Distributivity (basic) -}

  distrib : ∀{a b c} → (a +n b) ×n c ≡ (a ×n c) +n (b ×n c)
  distrib {Z} = refl
  distrib {S a}{b}{c} = plus-cong1 {b = c} (distrib {a}{b}{c})
                     ≡≡ plus-assoc {a ×n c}{b ×n c}{c}
                     ≡≡ plus-cong2 {a ×n c} (plus-comm {b ×n c} {c})
                     ≡≡ assoc-plus {a ×n c}{c}{b ×n c}

  {- Multiplication (simplification) -}

  zero-times : ∀{a} → 0 ×n a ≡ 0
  zero-times = refl

  times-zero : ∀{a} → a ×n 0 ≡ 0
  times-zero {Z} = refl
  times-zero {S a} = plus-cong1 (times-zero {a})

  succ-times : ∀{a b} → S a ×n b ≡ (a ×n b) +n b
  succ-times = refl

  times-succ : ∀{a b} → a ×n S b ≡ a +n (a ×n b)
  times-succ {Z} = refl
  times-succ {S a}{b} = plus-cong1 {b = S b} (times-succ {a}{b})
                     ≡≡ succ-plus {a +n (a ×n b)} {b}
                     ≡≡ succ-cong (plus-assoc {a}{a ×n b}{b})

  one-times : ∀{a} → 1 ×n a ≡ a
  one-times {a} = refl

  times-one : ∀{a} → a ×n 1 ≡ a
  times-one {a} = times-succ {a} ≡≡ plus-cong2 {a} (times-zero {a}) ≡≡ plus-zero

  {- Multimplication (rearrangement) -}

  times-comm : ∀{a b} → a ×n b ≡ b ×n a
  times-comm {Z}{b} = symm (times-zero {b})
  times-comm {S a}{b} = plus-comm {a ×n b}{b} 
                     ≡≡ plus-cong2 {b} (times-comm {a}{b}) 
                     ≡≡ symm (times-succ {b}{a})

  comm-times : ∀{a b} → b ×n a ≡ a ×n b
  comm-times {_}{a} = times-comm {a}

  times-assoc : ∀{a b c} → (a ×n b) ×n c ≡ a ×n (b ×n c)
  times-assoc {Z} = refl
  times-assoc {S a}{b}{c} = distrib {a ×n b}{b}{c}
                         ≡≡ plus-cong1 {b = b ×n c} (times-assoc {a}{b}{c})

  assoc-times : ∀{a b c} → a ×n (b ×n c) ≡ (a ×n b) ×n c
  assoc-times {a}{b}{c} = symm (times-assoc {a}{b}{c})

  {- Multiplication (equality) -}

  times-cong : ∀{a₁ a₂ b₁ b₂} → a₁ ≡ a₂ → b₁ ≡ b₂ → a₁ ×n b₁ ≡ a₂ ×n b₂
  times-cong Refl Refl = refl

  times-cong1 : ∀{a₁ a₂ b} → a₁ ≡ a₂ → a₁ ×n b ≡ a₂ ×n b
  times-cong1 Refl = refl

  times-cong2 : ∀{a b₁ b₂} → b₁ ≡ b₂ → a ×n b₁ ≡ a ×n b₂
  times-cong2 Refl = refl

  -- times-elim1 : ∀{a b c} → S a ×n b ≡ S a ×n c → b ≡ c
  -- times-elim2 : ∀{a b c} → b ×n S a ≡ c ×n S a → b ≡ c

  {- Distributivity -}

  distrib-right : ∀{a b c} → (a +n b) ×n c ≡ (a ×n c) +n (b ×n c)
  distrib-right {a}{b}{c} = distrib {a}{b}{c}

  distrib-left : ∀{a b c} → a ×n (b +n c) ≡ (a ×n b) +n (a ×n c)
  distrib-left {a}{b}{c} = times-comm {a} 
                        ≡≡ distrib {b}{c}{a} 
                        ≡≡ plus-cong (comm-times {a}{b}) (comm-times {a}{c})

  {- Cancellation -}

  plus-cancel : ∀{a b} → a +n b ≡ 0 → (a ≡ 0) × (b ≡ 0)
  plus-cancel {Z} Refl = refl , refl
  plus-cancel {S a} ()

  times-cancel : ∀{a b} → a ×n b ≡ 0 -> (a ≡ 0) + (b ≡ 0)
  times-cancel {Z} eq = Inl refl
  times-cancel {S a}{b} eq = Inr (snd (plus-cancel {a ×n b}{b} eq))

  {- Order -}

  _<_ : Nat → Nat → Set
  n < Z = VoidT
  Z < (S m) = UnitT
  (S n) < (S m) = n < m
  Lt = _<_

  _≤_ : Nat → Nat → Set
  Z ≤ n = UnitT
  (S n) ≤ Z = VoidT
  (S n) ≤ (S m) = n ≤ m
  Leq = _≤_

  _>_ : Nat → Nat → Set
  n > m = m < n
  Gt = _>_

  _≥_ : Nat → Nat → Set
  n ≥ m = m ≤ n
  Geq = _≥_

  _!≡_ : Nat → Nat → Set
  n !≡ m = (n < m) + (n > m)
  Neq = _!≡_

  {- Contradiction -}

  leq=>gt=>false : ∀{a b l} {A : Set l} → a ≤ b → a > b → A
  leq=>gt=>false {Z} leq () 
  leq=>gt=>false {S a}{Z} () gt
  leq=>gt=>false {S a}{S b} leq gt = leq=>gt=>false {a} {b} leq gt

  -- gt=>leq=>false : ∀{a b l} {A : Set l} → a > b → a ≤ b → A
  -- geq=>lt=>false : ∀{a b l} {A : Set l} → a ≥ b → a < b → A
  -- lt=>geq=>false : ∀{a b l} {A : Set l} → a < b → a ≥ b → A
  -- eq=>gt=>false  : ∀{a b l} {A : Set l} → a ≡ b → a > b → A
  -- gt=>eq=>false  : ∀{a b l} {A : Set l} → a > b → a ≡ b → A
  -- eq=>lt=>false  : ∀{a b l} {A : Set l} → a ≡ b → a < b → A
  -- lt=>eq=>false  : ∀{a b l} {A : Set l} → a < b → a ≡ b → A
  -- eq=>neq=>false : ∀{a b l} {A : Set l} → a ≡ b → a !≡ b → A
  -- neq=>eq=>false : ∀{a b l} {A : Set l} → a !≡ b → a ≡ b → A

  {- Options -}

  -- geq=>gt+eq : ∀{a b} → a ≥ b → (a > b) + (a ≡ b)
  -- geq=>eq+gt : ∀{a b} → a ≥ b → (a ≡ b) + (a > b)
  -- leq=>lt+eq : ∀{a b} → a ≤ b → (a < b) + (a ≡ b)
  -- leq=>eq+lt : ∀{a b} → a ≤ b → (a ≡ b) + (a < b)
  -- neq=>lt+gt : ∀{a b} → a !≡ b → (a < b) + (a > b)
  -- neq=>gt+lt : ∀{a b} → a !≡ b → (a > b) + (a < b)
  -- geq+lt     : ∀{a b} → (a ≥ b) + (a < b)
  -- lt+geq     : ∀{a b} → (a < b) + (a ≥ b)
  -- leq+gt     : ∀{a b} → (a ≤ b) + (a > b)
  -- gt+leq     : ∀{a b} → (a > b) + (a ≤ b)
  -- gt+eq+lt   : ∀{a b} → (a > b) + (a ≡ b) + (a < b)
  -- lt+eq+gt   : ∀{a b} → (a < b) + (a ≡ b) + (a > b)
  -- neq+eq     : ∀{a b} → (a !≡ b) + (a ≡ b)

  {- Weakening -}

  -- eq=>geq    : ∀{a b} → a ≡ b → a ≥ b
  -- eq=>leq    : ∀{a b} → a ≡ b → a ≤ b
  -- gt=>geq    : ∀{a b} → a > b → a ≥ b
  -- gt=>neq    : ∀{a b} → a > b → a !≡ b
  -- lt=>leq    : ∀{a b} → a < b → a ≤ b
  -- lt=>neq    : ∀{a b} → a < b → a !≡ b

  {- Strengthening -}

  -- neq=>geq=>gt : ∀{a b} → a !≡ b → a ≥ b → a > b
  -- geq=>neq=>gt : ∀{a b} → a ≥ b → a !≡ b → a > b
  -- neq=>leq=>lt : ∀{a b} → a !≡ b → a ≤ b → a < b
  -- leq=>neq=>lt : ∀{a b} → a ≤ b → a !≡ b → a < b
  -- geq=>leq=>eq : ∀{a b} → a ≥ b → a ≤ b → a ≡ b
  -- leq=>geq=>eq : ∀{a b} → a ≤ b → a ≥ b → a ≡ b

  {- Equivalency -}

  {- Working on both sides of an inequality -}
  
  {- Transitivity for inequality -}


open Nat public
  using (Z ; S ; _+n_ ; _×n_ ; _<_ ; _>_ ; _≤_ ; _≥_)
  renaming (Nat to NatT)