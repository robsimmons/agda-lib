{- Basic reasoning about natural numbers -}

module Demo.Arith where
 
open import Prelude

seven : 7 > 10 → ⊥
seven gt = gt

+comm : (n m : Nat) → (n +n m) ≡ (m +n n)
+comm n m = NAT.plus-comm {n}{m}

eq1 : (n m p : Nat) → (n +n (m +n p)) ≡ ((m +n n) +n p)
eq1 n m p = NAT.assoc-plus {n}{m}{p} ≡≡ NAT.plus-cong1 (+comm n m)
  
append : List Nat → List Nat → List Nat
append [] ys = ys
append (x :: xs) ys = x :: append xs ys

inapp : ∀{x} (xs ys : List Nat) → x ∈ ys → x ∈ append xs ys
inapp [] ys n = n
inapp (x :: xs) ys n = S (inapp xs ys n)
