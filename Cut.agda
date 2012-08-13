
open import Prelude hiding (⊥)
open import Foc

module Cut where

subst⁺ : ∀{A U Γ Ω}
  → Γ suspnormalΓ
  → U suspnormalR 
  → Value Γ A
  → Term Γ (A :: Ω) U
  → Term Γ Ω U

subst⁻ : ∀{U A Γ} 
  → Γ suspnormalΓ
  → U suspnormalR
  → Term Γ [] (Inv A)
  → Spine Γ A U
  → Term Γ [] U

rsubst : ∀{Γ A Form} (Γ' : Ctx)
  → (Γ' ++ Γ) suspnormalΓ
  → Form suspnormalF 
  → Term (Γ' ++ Γ) [] (Inv A)
  → Exp (Γ' ++ (Pers A) :: Γ) Form
  → Exp (Γ' ++ Γ) Form

lsubstN : ∀{Γ U Ω A} (Γ' : Ctx)
  → (Γ' ++ Γ) suspnormalΓ
  → U suspnormalR
  → Term (Γ' ++ Γ) Ω (True A)
  → Term (Γ' ++ Γ) [ A ] U
  → Term (Γ' ++ Γ) Ω U

lsubstSp : ∀{Γ U B A} (Γ' : Ctx)
  → (Γ' ++ Γ) suspnormalΓ
  → U suspnormalR
  → Spine (Γ' ++ Γ) B (True A)
  → Term (Γ' ++ Γ) [ A ] U
  → Spine (Γ' ++ Γ) B U

-- Positive principal substitution
subst⁺ {A} pfΓ pfU (id⁺ x) N with pfΓ x
subst⁺ {a Q .⁺} pfΓ pfU (id⁺ x) (η⁺ N) | pf = fsub⁺ [] (id⁺ x) N
subst⁺ {↓ A} pfΓ pfU (id⁺ x) N | ()
subst⁺ {⊥} pfΓ pfU (id⁺ x) N | ()
subst⁺ {A ∨ B} pfΓ pfU (id⁺ x) N | ()
subst⁺ {⊤⁺} pfΓ pfU (id⁺ x) N | ()
subst⁺ {A ∧⁺ B} pfΓ pfU (id⁺ x) N | ()
subst⁺ pfΓ pfU (↓R N) (↓L N') = rsubst [] pfΓ pfU N N'
subst⁺ pfΓ pfU (∨R₁ V) (∨L N₁ N₂) = subst⁺ pfΓ pfU V N₁
subst⁺ pfΓ pfU (∨R₂ V) (∨L N₁ N₂) = subst⁺ pfΓ pfU V N₂
subst⁺ pfΓ pfU ⊤⁺R (⊤⁺L N) = N
subst⁺ pfΓ pfU (∧⁺R V₁ V₂) (∧⁺L N) = subst⁺ pfΓ pfU V₂ (subst⁺ pfΓ pfU V₁ N)

-- Negative principle substitution
subst⁻ pfΓ pfU (focusL () x Sp') Sp 
subst⁻ pfΓ pfU (η⁻ N) id⁻ = N
subst⁻ pfΓ () N (id⁻ {↑ A}) 
subst⁻ pfΓ () N (id⁻ {A ⊃ B})
subst⁻ pfΓ () N (id⁻ {⊤⁻})
subst⁻ pfΓ () N (id⁻ {A ∧⁻ B})
subst⁻ pfΓ pfU (↑R N) (↑L N') = lsubstN [] pfΓ pfU N N'
subst⁻ pfΓ pfU (⊃R N) (⊃L V Sp) = subst⁻ pfΓ pfU (subst⁺ pfΓ <> V N) Sp
subst⁻ pfΓ pfU (∧⁻R N₁ N₂) (∧⁻L₁ Sp) = subst⁻ pfΓ pfU N₁ Sp
subst⁻ pfΓ pfU (∧⁻R N₁ N₂) (∧⁻L₂ Sp) = subst⁻ pfΓ pfU N₂ Sp

-- Substitution into values
rsubst Γ' pfΓ pfF N (id⁺ x) with fromctx Γ' x 
... | Inl () 
... | Inr x' = id⁺ x'
rsubst Γ' pfΓ pfF N (↓R N') = ↓R (rsubst Γ' pfΓ pfF N N')
rsubst Γ' pfΓ pfF N (∨R₁ V) = ∨R₁ (rsubst Γ' pfΓ pfF N V)
rsubst Γ' pfΓ pfF N (∨R₂ V) = ∨R₂ (rsubst Γ' pfΓ pfF N V)
rsubst Γ' pfΓ pfF N ⊤⁺R = ⊤⁺R
rsubst Γ' pfΓ pfF N (∧⁺R V₁ V₂) = 
  ∧⁺R (rsubst Γ' pfΓ pfF N V₁) (rsubst Γ' pfΓ pfF N V₂)

-- Substitution into terms
rsubst Γ' pfΓ pfF N (focusR V) = focusR (rsubst Γ' pfΓ pfF N V)
rsubst Γ' pfΓ pfF N (focusL pf⁻ x Sp) with fromctx Γ' x
... | Inl Refl = subst⁻ pfΓ pfF N (rsubst Γ' pfΓ pfF N Sp)
... | Inr x' = focusL pf⁻ x' (rsubst Γ' pfΓ pfF N Sp)
rsubst Γ' pfΓ pfF N (η⁺ N') = 
  η⁺ (rsubst (_ :: Γ') {!!} pfF (wk LIST.SET.sub-wken N) N')
rsubst Γ' pfΓ pfF N (η⁻ N') = η⁻ (rsubst Γ' pfΓ pfF N N')
rsubst Γ' pfΓ pfF N (↓L N') = 
  ↓L (rsubst (_ :: Γ') {!!} pfF (wk LIST.SET.sub-wken N) N')
rsubst Γ' pfΓ pfF N (↑R N') = ↑R (rsubst Γ' pfΓ pfF N N')
rsubst Γ' pfΓ pfF N ⊥L = ⊥L
rsubst Γ' pfΓ pfF N (∨L N₁ N₂) =
  ∨L (rsubst Γ' pfΓ pfF N N₁) (rsubst Γ' pfΓ pfF N N₂)
rsubst Γ' pfΓ pfF N (⊤⁺L N') = ⊤⁺L (rsubst Γ' pfΓ pfF N N')
rsubst Γ' pfΓ pfF N (∧⁺L N') = ∧⁺L (rsubst Γ' pfΓ pfF N N')
rsubst Γ' pfΓ pfF N (⊃R N') = ⊃R (rsubst Γ' pfΓ pfF N N')
rsubst Γ' pfΓ pfF N ⊤⁻R = ⊤⁻R
rsubst Γ' pfΓ pfF N (∧⁻R N₁ N₂) = 
  ∧⁻R (rsubst Γ' pfΓ pfF N N₁) (rsubst Γ' pfΓ pfF N N₂)

-- Substitution into spines
rsubst Γ' pfΓ pfF N id⁻ = id⁻
rsubst Γ' pfΓ pfF N (↑L N') = ↑L (rsubst Γ' pfΓ pfF N N')
rsubst Γ' pfΓ pfF N (⊃L V Sp) = 
  ⊃L (rsubst Γ' pfΓ <> N V) (rsubst Γ' pfΓ pfF N Sp)
rsubst Γ' pfΓ pfF N (∧⁻L₁ Sp) = ∧⁻L₁ (rsubst Γ' pfΓ pfF N Sp)
rsubst Γ' pfΓ pfF N (∧⁻L₂ Sp) = ∧⁻L₂ (rsubst Γ' pfΓ pfF N Sp)

-- Substitution out of terms
lsubstN Γ' pfΓ pfU (focusR V) N = subst⁺ pfΓ pfU V N
lsubstN Γ' pfΓ pfU (focusL pf⁻ x Sp) N = 
  focusL {!pfU implies stable!} x (lsubstSp Γ' pfΓ pfU Sp N)
lsubstN Γ' pfΓ pfU (η⁺ N) N' =
  η⁺ (lsubstN (_ :: Γ') {!!} pfU N (wk LIST.SET.sub-wken N'))
lsubstN Γ' pfΓ pfU (↓L N) N' =
  ↓L (lsubstN (_ :: Γ') {!!} pfU N (wk LIST.SET.sub-wken N'))
lsubstN Γ' pfΓ pfU ⊥L N = ⊥L
lsubstN Γ' pfΓ pfU (∨L N₁ N₂) N = 
  ∨L (lsubstN Γ' pfΓ pfU N₁ N) (lsubstN Γ' pfΓ pfU N₂ N)
lsubstN Γ' pfΓ pfU (⊤⁺L N) N' = ⊤⁺L (lsubstN Γ' pfΓ pfU N N')
lsubstN Γ' pfΓ pfU (∧⁺L N) N' = ∧⁺L (lsubstN Γ' pfΓ pfU N N')

-- Substitution out of spines 
lsubstSp Γ' pfΓ pfU (↑L N) N' = ↑L (lsubstN Γ' pfΓ pfU N N')
lsubstSp Γ' pfΓ pfU (⊃L V Sp) N = ⊃L V (lsubstSp Γ' pfΓ pfU Sp N)
lsubstSp Γ' pfΓ pfU (∧⁻L₁ Sp) N = ∧⁻L₁ (lsubstSp Γ' pfΓ pfU Sp N)
lsubstSp Γ' pfΓ pfU (∧⁻L₂ Sp) N = ∧⁻L₂ (lsubstSp Γ' pfΓ pfU Sp N)
