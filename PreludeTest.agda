

module PreludeTest where
 
  open import Prelude

  a : Unit0 × Unit0 → Unit0 × Unit0 × Unit0
  a (p1 , p2) = p1 , p1 , p1

  {- Unit for void using  -}
  b : ∀{A} → A + Void0 → A
  b x = case x (λ x → x) (λ x → abort x)

  {- -}
  c : ∀{A} → A + Void0 → A
  c (Inl x) = x
  c (Inr ()) 

