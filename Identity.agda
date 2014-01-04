
open import Prelude hiding (⊥; ⊤)
open import Foc

module Identity where

-- Identity expansion

expand⁺ : ∀{A Γ Ω U} → Term (Susp A :: Γ) Ω U → Term Γ (A :: Ω) U
expand⁻ : ∀{A Γ} → Term Γ [] (Susp A) → Term Γ [] (Inv A)

expand⁺ {a Q .⁺} N = η⁺ N
expand⁺ {↓ A} N = 
  ↓L (subst⁺ [] (↓R (expand⁻ (focL <> Z id⁻))) (wkex N))
expand⁺ {⊥} N = ⊥L
expand⁺ {A ∨ A₁} N = 
  ∨L (expand⁺ (subst⁺ [] (∨R₁ (id⁺ Z)) (wkex N))) 
    (expand⁺ (subst⁺ [] (∨R₂ (id⁺ Z)) (wkex N)))
expand⁺ {⊤⁺} N = ⊤⁺L (subst⁺ [] ⊤⁺R N)
expand⁺ {A ∧⁺ A₁} N = 
  ∧⁺L (expand⁺ 
        (expand⁺ 
          (subst⁺ [] (∧⁺R (id⁺ (S Z)) (id⁺ Z)) (wkex (wkex N)))))

expand⁻ {a Q .⁻} N = η⁻ N
expand⁻ {↑ A} N = ↑R (subst⁻ <> N (↑L (expand⁺ (focR (id⁺ Z)))))
expand⁻ {A ⊃ A₁} N = 
  ⊃R (expand⁺ (expand⁻ (subst⁻ <> (wken N) (⊃L (id⁺ Z) id⁻))))
expand⁻ {⊤⁻} N = ⊤⁻R
expand⁻ {A ∧⁻ A₁} N = 
  ∧⁻R (expand⁻ (subst⁻ <> N (∧⁻L₁ id⁻))) (expand⁻ (subst⁻ <> N (∧⁻L₂ id⁻)))
