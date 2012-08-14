
open import Prelude hiding (⊥; ⊤)
open import Foc

module Identity where

-- Focal substitution

-- Values substituted in for suspended positive propositions

subst⁺ : ∀{Γ A Form} (Γ' : Ctx)
  → Value (Γ' ++ Γ) A
  → Exp (Γ' ++ Susp A :: Γ) Form
  → Exp (Γ' ++ Γ) Form

subst⁺ Γ' V (id⁺ x) with fromctx Γ' x
... | Inl Refl = V
... | Inr x' = id⁺ x'
subst⁺ Γ' V (↓R N) = ↓R (subst⁺ Γ' V N)
subst⁺ Γ' V (∨R₁ V') = ∨R₁ (subst⁺ Γ' V V')
subst⁺ Γ' V (∨R₂ V') = ∨R₂ (subst⁺ Γ' V V')
subst⁺ Γ' V ⊤⁺R = ⊤⁺R
subst⁺ Γ' V (∧⁺R V₁ V₂) = ∧⁺R (subst⁺ Γ' V V₁) (subst⁺ Γ' V V₂)

subst⁺ Γ' V (focusR V') = focusR (subst⁺ Γ' V V')
subst⁺ Γ' V (focusL pf x Sp) with fromctx Γ' x
... | Inl ()
... | Inr x' = focusL pf x' (subst⁺ Γ' V Sp)
subst⁺ Γ' V (η⁺ N) = η⁺ (subst⁺ (_ :: Γ') (wken V) N)
subst⁺ Γ' V (η⁻ N) = η⁻ (subst⁺ Γ' V N)
subst⁺ Γ' V (↓L N) = ↓L (subst⁺ (_ :: Γ') (wken V) N)
subst⁺ Γ' V (↑R N) = ↑R (subst⁺ Γ' V N)
subst⁺ Γ' V ⊥L = ⊥L
subst⁺ Γ' V (∨L N₁ N₂) = ∨L (subst⁺ Γ' V N₁) (subst⁺ Γ' V N₂)
subst⁺ Γ' V (⊤⁺L N) = ⊤⁺L (subst⁺ Γ' V N)
subst⁺ Γ' V (∧⁺L N) = ∧⁺L (subst⁺ Γ' V N)
subst⁺ Γ' V (⊃R N) = ⊃R (subst⁺ Γ' V N)
subst⁺ Γ' V ⊤⁻R = ⊤⁻R
subst⁺ Γ' V (∧⁻R N₁ N₂) = ∧⁻R (subst⁺ Γ' V N₁) (subst⁺ Γ' V N₂)

subst⁺ Γ' V id⁻ = id⁻
subst⁺ Γ' V (↑L N) = ↑L (subst⁺ Γ' V N)
subst⁺ Γ' V (⊃L V' Sp) = ⊃L (subst⁺ Γ' V V') (subst⁺ Γ' V Sp)
subst⁺ Γ' V (∧⁻L₁ Sp) = ∧⁻L₁ (subst⁺ Γ' V Sp)
subst⁺ Γ' V (∧⁻L₂ Sp) = ∧⁻L₂ (subst⁺ Γ' V Sp)

-- Spines substituted out for suspended negative propositions

subst⁻ : ∀{Γ A L U}
  → U stableR
  → Exp Γ (Left L (Susp A))
  → Spine Γ A U
  → Exp Γ (Left L U)

subst⁻ pf (focusL _ x Sp) Sp' = focusL pf x (subst⁻ pf Sp Sp')
subst⁻ pf (η⁺ N) Sp = η⁺ (subst⁻ pf N (wken Sp))
subst⁻ pf (↓L N) Sp = ↓L (subst⁻ pf N (wken Sp))
subst⁻ pf ⊥L Sp = ⊥L
subst⁻ pf (∨L N₁ N₂) Sp = ∨L (subst⁻ pf N₁ Sp) (subst⁻ pf N₂ Sp)
subst⁻ pf (⊤⁺L N) Sp = ⊤⁺L (subst⁻ pf N Sp)
subst⁻ pf (∧⁺L N) Sp = ∧⁺L (subst⁻ pf N Sp)

subst⁻ pf id⁻ Sp = Sp
subst⁻ pf (↑L N) Sp = ↑L (subst⁻ pf N Sp)
subst⁻ pf (⊃L V Sp) Sp' = ⊃L V (subst⁻ pf Sp Sp')
subst⁻ pf (∧⁻L₁ Sp) Sp' = ∧⁻L₁ (subst⁻ pf Sp Sp')
subst⁻ pf (∧⁻L₂ Sp) Sp' = ∧⁻L₂ (subst⁻ pf Sp Sp')

-- Identity expansion

expand⁺ : ∀{A Γ Ω U} → Term (Susp A :: Γ) Ω U → Term Γ (A :: Ω) U
expand⁻ : ∀{A Γ} → Term Γ [] (Susp A) → Term Γ [] (Inv A)

expand⁺ {a Q .⁺} N = η⁺ N
expand⁺ {↓ A} N = 
  ↓L (subst⁺ [] (↓R (expand⁻ (focusL <> Z id⁻))) (wk LIST.SET.sub-wkex N))
expand⁺ {⊥} N = ⊥L 
expand⁺ {A ∨ B} N = 
  ∨L (expand⁺ (subst⁺ [] (∨R₁ (id⁺ Z)) (wk LIST.SET.sub-wkex N)))
    (expand⁺ (subst⁺ [] (∨R₂ (id⁺ Z)) (wk LIST.SET.sub-wkex N)))
expand⁺ {⊤⁺} N = ⊤⁺L (subst⁺ [] ⊤⁺R N)
expand⁺ {A ∧⁺ B} N = 
  ∧⁺L (expand⁺
        (expand⁺
          (subst⁺ [] (∧⁺R (id⁺ (S Z)) (id⁺ Z))
            (wk LIST.SET.sub-wkex (wk LIST.SET.sub-wkex N)))))

expand⁻ {a Q .⁻} N = η⁻ N
expand⁻ {↑ A} N = ↑R (subst⁻ <> N (↑L (expand⁺ (focusR (id⁺ Z)))))
expand⁻ {A ⊃ B} N = 
  ⊃R (expand⁺ (expand⁻ (subst⁻ <> (wken N) (⊃L (id⁺ Z) id⁻))))
expand⁻ {⊤⁻} N = ⊤⁻R
expand⁻ {A ∧⁻ B} N = 
  ∧⁻R (expand⁻ (subst⁻ <> N (∧⁻L₁ id⁻))) (expand⁻ (subst⁻ <> N (∧⁻L₂ id⁻)))

