module LangT where

open import Prelude hiding ([_])
open import Lambda
open import Lang
open import GoedelT

module LANG-T where


  data Atom : Set where
    nat : Atom
    bool : Atom

  open TYPES Atom public

  data Const : Set where
    true : Const
    false : Const
    z : Const
    s : Const

  sig : Const → VType ⁻
  sig true = con bool
  sig false = con bool
  sig z = con nat
  sig s = ⟨ con nat ⟩ ⊃ con nat

  open TERMS Atom Const sig public renaming (wk to wkN ; subst to substN) 
  open LANG Atom Const sig public 

  abort₁ : ∀{Δ A B C} {Any : Set} → Neut Δ [] (A ⊃ B ⊃ C) → Any
  abort₁ (var ()) 
  abort₁ (R ·' x) = abort₁ R
  abort₁ (con true ())
  abort₁ (con false ())
  abort₁ (con z ())
  abort₁ (con s ()) 
  abort₁ (R · N) = abort₁ R

  abort₂ : ∀{Δ A B} {Any : Set} → Neut Δ [] (U A ⊃ B) → Any
  abort₂ (var ())
  abort₂ (R ·' x) = abort₂ R
  abort₂ (con true ())
  abort₂ (con false ())
  abort₂ (con z ())
  abort₂ (con s ())
  abort₂ (R · N) = abort₁ R

  encodeN : Nat → Norm [] [] (con nat)
  encodeN Z = ⟨ con z refl ⟩
  encodeN (S n) = ⟨ con s refl · encodeN n ⟩

  decodeN : ∀{Γ} → Norm Γ [] (con nat) → Nat
  decodeN ⟨ var () ⟩ 
  decodeN ⟨ R ·' u ⟩ = abort₂ R
  decodeN ⟨ con true () ⟩ 
  decodeN ⟨ con false () ⟩
  decodeN ⟨ con z Refl ⟩ = Z
  decodeN ⟨ con s () ⟩
  decodeN ⟨ var () · N ⟩
  decodeN ⟨ R ·' u · N' ⟩ = abort₂ R
  decodeN ⟨ con true () · N ⟩ 
  decodeN ⟨ con false () · N ⟩
  decodeN ⟨ con z () · N ⟩
  decodeN ⟨ con s Refl · N ⟩ = S (decodeN N)
  decodeN ⟨ R · N · N' ⟩ = abort₁ R

  decodeB : ∀{Γ} → Norm Γ [] (con bool) → Bool
  decodeB ⟨ var () ⟩ 
  decodeB ⟨ R ·' u ⟩ = abort₂ R
  decodeB ⟨ con true Refl ⟩ = True 
  decodeB ⟨ con false Refl ⟩ = False
  decodeB ⟨ con z () ⟩
  decodeB ⟨ con s () ⟩
  decodeB ⟨ var () · N ⟩
  decodeB ⟨ R ·' u · N' ⟩ = abort₂ R
  decodeB ⟨ con true () · N ⟩ 
  decodeB ⟨ con false () · N ⟩
  decodeB ⟨ con z () · N ⟩
  decodeB ⟨ con s () · N ⟩
  decodeB ⟨ R · N · N' ⟩ = abort₁ R




module EQUIV-T where

  open LANG-T 
  open GÖDEL-T renaming (subst to substT ; wk to wkT)

  encode : TTp → CType
  encode nat = F (con nat)
  encode bool = F (con bool)
  encode (A ⇒ B) = encode A ⇒ encode B

  idsub : ∀{Γ} (Δp : VCtx) → Subst (Δp +>> Γ) (Δp)
  idsub [] = ⟨⟩
  idsub (A :: Δp) = var (sub-revappendl _ Δp Z) , idsub Δp

  embed : ∀{Γ A} → TExp Γ A → Exp (LIST.map encode Γ) (encode A)
  embed (var x) = var (LIST.in-map encode x)
  embed (Λ e) = Λ embed e
  embed (e₁ · e₂) = embed e₁ · embed e₂
  embed true = ⟨ con true refl ⟩ [ ⟨⟩ ]
  embed false = ⟨ con false refl ⟩ [ ⟨⟩ ]
  embed {Γ} {A} (ite e et ef) = 
    elim (embed e) 
      (λ {Δp} N → 
        if (λ _ → Exp (Δp +>> LIST.map encode Γ) (encode A)) / decodeB N
        then (wk (sub-revappendl _ Δp) (embed et))
        else (wk (sub-revappendl _ Δp) (embed ef)))
  embed z = ⟨ con z refl ⟩ [ ⟨⟩ ]
  embed (s e) = 
    elim (embed e) (λ {Δp} N → ⟨ con s refl · N ⟩ [ idsub Δp ])
  embed {Γ} {A} (rec e eb ei) = 
    elim (embed e) 
      (λ {Δp} N → 
        NAT.fold {λ _ → Exp (Δp +>> LIST.map encode Γ) (encode A)}
          (wk (sub-revappendl _ Δp) (embed eb)) 
          (λ n x →  
            subst [] ((encodeN n [ ⟨⟩ ]) , x , ⟨⟩) 
              (wk (LIST.SET.sub-cons-congr
                    (LIST.SET.sub-cons-congr (sub-revappendl _ Δp))) 
                (embed ei)))
          (decodeN N))
 

