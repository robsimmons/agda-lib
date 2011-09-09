open import Prelude

module Identitytypes where

+commutes : (n m : Nat) → (n +n m) ≡ (m +n n)
+commutes Z m = {!!}
+commutes (S n) m = {!!}

s-cong : (n m : Nat) → n ≡ m → Id {_} {Nat} (S n) (S m)
s-cong n m eq = {!!}