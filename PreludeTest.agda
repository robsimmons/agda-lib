

module PreludeTest where
 
  open import Prelude

  {- Units being units -}
  a : ∀{A : Set0} → ⊤ × A × ⊤ → A × ⊤ × ⊤ × ⊤ × A
  a (p1 , p2 , <>) = p2 , <> , <> , p1 , p2

  {- Unit for void using the elimination forms -}
  b : ∀{A} → A + ⊥ → A
  b x = case x (λ x → x) (λ x → abort x)

  {- Unit vor void using pattern matching -}
  c : ∀{A} → A + ⊥ → A
  c (Inl x) = x
  c (Inr ()) 

  {- All units are equal -}
  d : (x y : ⊤) → x ≡ y
  d <> <> = Refl

  e : (x y : ⊤) → x ≡ y
  e x y = d x x ≡≡ d x y ≡≡ d y y

  {- Some number reasoning -}
  f : 7 > 10 → ⊥
  f gt = gt
  
  g : (n m : NatT) → (n +n m) ≡ (m +n n)
  g n m = Nat.plus-comm {n}{m}
  
  h : (n m p : NatT) → (n +n (m +n p)) ≡ ((m +n n) +n p)
  h n m p = Nat.assoc-plus {n}{m}{p} ≡≡ Nat.plus-cong1 (g n m)

  i : {A B : Set} → A + B → B + A
  i (Inl x) = Inr x
  i (Inr x) = Inl x