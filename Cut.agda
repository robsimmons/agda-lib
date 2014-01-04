
open import Prelude hiding (⊥)
open import Foc

module Cut where

cut⁺ : ∀{A U Γ Ω}
  → suspnormalΓ Γ
  → suspnormal U
  → Value Γ A
  → Term Γ (A :: Ω) U
  → Term Γ Ω U

cut⁻ : ∀{U A Γ} 
  → suspnormalΓ Γ 
  → suspstable U
  → Term Γ [] (Inv A)
  → Spine Γ A U
  → Term Γ [] U

rsubst : ∀{Γ A Form} (Γ' : Ctx)
  → suspnormalΓ (Γ' ++ Γ)
  → suspnormalF Form
  → Term (Γ' ++ Γ) [] (Inv A)
  → Exp (Γ' ++ (Pers A) :: Γ) Form
  → Exp (Γ' ++ Γ) Form

lsubst : ∀{Γ U L A} 
  → suspnormalΓ Γ
  → suspstable U
  → Exp Γ (Left L (True A))
  → Term Γ [ A ] U 
  → Exp Γ (Left L U)

-- Positive principal substitution
cut⁺ pfΓ pf (id⁺ x) N with pfΓ x
cut⁺ pfΓ pf (id⁺ x) (η⁺ N) | (_ , Refl) = subst⁺ [] (id⁺ x) N
cut⁺ pfΓ pf (↓R M) (↓L N) = rsubst [] pfΓ pf M N
cut⁺ pfΓ pf (∨R₁ V) (∨L N₁ N₂) = cut⁺ pfΓ pf V N₁
cut⁺ pfΓ pf (∨R₂ V) (∨L N₁ N₂) = cut⁺ pfΓ pf V N₂
cut⁺ pfΓ pf ⊤⁺R (⊤⁺L N) = N
cut⁺ pfΓ pf (∧⁺R V₁ V₂) (∧⁺L N) = cut⁺ pfΓ pf V₂ (cut⁺ pfΓ pf V₁ N)

-- Negative principle substitution
cut⁻ pfΓ pf (focL () x Sp') Sp 
cut⁻ pfΓ pf (η⁻ N) id⁻ = N
cut⁻ pfΓ (_ , ()) N (id⁻ {↑ A}) 
cut⁻ pfΓ (_ , ()) N (id⁻ {A ⊃ B})
cut⁻ pfΓ (_ , ()) N (id⁻ {⊤⁻})
cut⁻ pfΓ (_ , ()) N (id⁻ {A ∧⁻ B})
cut⁻ pfΓ pf (↑R N) (↑L M) = lsubst pfΓ pf N M
cut⁻ pfΓ pf (⊃R N) (⊃L V Sp) = cut⁻ pfΓ pf (cut⁺ pfΓ <> V N) Sp
cut⁻ pfΓ pf (∧⁻R N₁ N₂) (∧⁻L₁ Sp) = cut⁻ pfΓ pf N₁ Sp
cut⁻ pfΓ pf (∧⁻R N₁ N₂) (∧⁻L₂ Sp) = cut⁻ pfΓ pf N₂ Sp

-- Substitution into values
rsubst Γ' pfΓ pf M (id⁺ z) with fromctx Γ' z
... | Inl ()
... | Inr z' = id⁺ z'
rsubst Γ' pfΓ pf M (↓R N) = ↓R (rsubst Γ' pfΓ pf M N)
rsubst Γ' pfΓ pf M (∨R₁ V) = ∨R₁ (rsubst Γ' pfΓ pf M V)
rsubst Γ' pfΓ pf M (∨R₂ V) = ∨R₂ (rsubst Γ' pfΓ pf M V)
rsubst Γ' pfΓ pf M ⊤⁺R = ⊤⁺R
rsubst Γ' pfΓ pf M (∧⁺R V₁ V₂) = 
  ∧⁺R (rsubst Γ' pfΓ pf M V₁) (rsubst Γ' pfΓ pf M V₂)

-- Substitution into terms
rsubst Γ' pfΓ pf M (focR V) = focR (rsubst Γ' pfΓ pf M V)
rsubst Γ' pfΓ pf M (focL pf' x' Sp) with fromctx Γ' x'
... | Inl Refl = cut⁻ pfΓ (pf' , pf) M (rsubst Γ' pfΓ pf M Sp)
... | Inr x = focL pf' x (rsubst Γ' pfΓ pf M Sp)
rsubst Γ' pfΓ pf M (η⁺ N) = η⁺ (rsubst (_ :: Γ') (conssusp pfΓ) pf (wken M) N)
rsubst Γ' pfΓ pf M (↓L N) = ↓L (rsubst (_ :: Γ') (conspers pfΓ) pf (wken M) N)
rsubst Γ' pfΓ pf M ⊥L = ⊥L
rsubst Γ' pfΓ pf M (∨L N₁ N₂) = 
  ∨L (rsubst Γ' pfΓ pf M N₁) (rsubst Γ' pfΓ pf M N₂)
rsubst Γ' pfΓ pf M (⊤⁺L N) = ⊤⁺L (rsubst Γ' pfΓ pf M N)
rsubst Γ' pfΓ pf M (∧⁺L N) = ∧⁺L (rsubst Γ' pfΓ pf M N)
rsubst Γ' pfΓ pf M (η⁻ N) = η⁻ (rsubst Γ' pfΓ pf M N)
rsubst Γ' pfΓ pf M (↑R N) = ↑R (rsubst Γ' pfΓ pf M N)
rsubst Γ' pfΓ pf M (⊃R N) = ⊃R (rsubst Γ' pfΓ pf M N)
rsubst Γ' pfΓ pf M ⊤⁻R = ⊤⁻R
rsubst Γ' pfΓ pf M (∧⁻R N₁ N₂) =
  ∧⁻R (rsubst Γ' pfΓ pf M N₁) (rsubst Γ' pfΓ pf M N₂)

-- Substitution into spines
rsubst Γ' pfΓ pf M id⁻ = id⁻
rsubst Γ' pfΓ pf M (↑L N) = ↑L (rsubst Γ' pfΓ pf M N)
rsubst Γ' pfΓ pf M (⊃L V Sp) =
  ⊃L (rsubst Γ' pfΓ <> M V) (rsubst Γ' pfΓ pf M Sp)
rsubst Γ' pfΓ pf M (∧⁻L₁ Sp) = ∧⁻L₁ (rsubst Γ' pfΓ pf M Sp)
rsubst Γ' pfΓ pf M (∧⁻L₂ Sp) = ∧⁻L₂ (rsubst Γ' pfΓ pf M Sp)

-- Substitution out of terms
lsubst pfΓ pf (focR V) N = cut⁺ pfΓ (snd pf) V N
lsubst pfΓ pf (focL pf' x Sp) N = focL (fst pf) x (lsubst pfΓ pf Sp N) 
lsubst pfΓ pf (η⁺ M) N = η⁺ (lsubst (conssusp pfΓ) pf M (wken N))
lsubst pfΓ pf (↓L M) N = ↓L (lsubst (conspers pfΓ) pf M (wken N))
lsubst pfΓ pf ⊥L M = ⊥L
lsubst pfΓ pf (∨L M₁ M₂) N = ∨L (lsubst pfΓ pf M₁ N) (lsubst pfΓ pf M₂ N)
lsubst pfΓ pf (⊤⁺L M) N = ⊤⁺L (lsubst pfΓ pf M N)
lsubst pfΓ pf (∧⁺L M) N = ∧⁺L (lsubst pfΓ pf M N)

-- Substitution of of spines
lsubst pfΓ pf (↑L M) N = ↑L (lsubst pfΓ pf M N)
lsubst pfΓ pf (⊃L V Sp) N = ⊃L V (lsubst pfΓ pf Sp N)
lsubst pfΓ pf (∧⁻L₁ Sp) N = ∧⁻L₁ (lsubst pfΓ pf Sp N)
lsubst pfΓ pf (∧⁻L₂ Sp) N = ∧⁻L₂ (lsubst pfΓ pf Sp N)

