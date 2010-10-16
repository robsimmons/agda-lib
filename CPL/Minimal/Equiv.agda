-- K4W⁻ Natural Deduction
-- A Constructive Logic of Provability
-- Robert J. Simmons, Bernardo Toninho

open import Compat
open import Accessibility.Inductive 
import Accessibility.IndexedList as IndexedList 
import Minimal.Core as Core 
import Minimal.Sequent as Sequent
import Minimal.NatDeduction as NatDeduction

module Minimal.Equiv (UWF : UpwardsWellFounded) where

  open SuccStar UWF
  open IndexedList UWF
  open Core UWF 
  open Sequent UWF 
  open NatDeduction UWF 

  {- Unnecessary lemmas in the wrong place -}

  ≺+⊀trans : ∀{w₁ w₂ w₃} → w₁ ≺+ w₂ → w₁ ⊀ w₃ → w₂ ⊀ w₃
  ≺+⊀trans ω nω ≺*≡ = nω (≺*+ ω)
  ≺+⊀trans ω nω (≺*+ ω') = nω (≺*+ (≺+trans ω ω'))

  ⊆to/wkenirrev : ∀{A Γ Δ w w'}{x : A}
       → w ⊀ w'
       → Δ ⊆ Γ to w 
       → Δ ⊆ ((x at w') ∷ Γ) to w
  ⊆to/wkenirrev ω (st sub sub≺) 
   = st (⊆at/wken (λ iN → sub iN)) 
        (λ ω' → ⊆at/irrev (≺+⊀trans ω' ω) (sub≺ ω'))

  {- Lemmas -}

  wkto : ∀{w w' Γ A} → w ≺ w' → (Γ , A [ w ]) ⊆ Γ to w'
  wkto ω = ⊆to/irrev (≺⊀ ω) (⊆to/refl _) 

  wkto' : ∀{w w' Γ A} → w ≺ w' → Γ ⊆ (Γ , A [ w ]) to w'
  wkto' ω = ⊆to/wkenirrev (≺⊀ ω) (⊆to/refl _)

  wk-nd : ∀ {Γ Δ A w} → Γ ⊆ Δ to w → Γ ⊢ A [ w ] → Δ ⊢ A [ w ] 
  wk-nd = NatDeduction.wk UWF

  wk-seq : ∀ {Γ Δ A w} → Γ ⊆ Δ to w → Γ ⇒ A [ w ] → Δ ⇒ A [ w ] 
  wk-seq = Sequent.wk UWF



  {- Equivalence of natural deduction and sequent calculus -}

  equivP : W → Set
  equivP = 
   λ w → ((∀{Γ A} → Γ ⊢ A [ w ] → Γ ⇒ A [ w ]) ×
          (∀{Γ A} → Γ ⇒ A [ w ] → Γ ⊢ A [ w ]))

  nd→seq' : (w : W) → ((w' : W) → w ≺ w' → equivP w')
             → ∀{Γ A} → Γ ⊢ A [ w ] → Γ ⇒ A [ w ]
  nd→seq' w ih (hyp iN) = iden' _ iN
  nd→seq' w ih (⊃I D) = ⊃R (nd→seq' w ih D)
  nd→seq' w ih (⊃E D D')
   = cut (nd→seq' w ih D')
      (cut (wk-seq wken (nd→seq' w ih D)) 
        (⊃L i0 (iden' _ (iS i0)) (iden _)))
  nd→seq' w ih (□I D) = □R (λ ω → proj₁ (ih _ ω) (D ω))
  nd→seq' w ih (□E D D')
   = cut (nd→seq' w ih D)
      (□L i0 (λ D₀ → wk-seq wken (nd→seq' w ih 
        (D' (λ ω → proj₂ (ih _ ω) (wk-seq (wkto ω) (D₀ ω)))))))
  nd→seq' w ih (◇I ω D) = ◇R ω (proj₁ (ih _ ω) D)
  nd→seq' w ih (◇E D D') 
   = cut (nd→seq' w ih D) 
      (◇L i0 (λ ω D₀ → wk-seq wken (nd→seq' w ih 
        (D' ω (proj₂ (ih _ ω) (wk-seq (wkto ω) D₀))))))
  nd→seq' w ih (¬□I D) = ¬□R (λ ω D₀ → D ω (proj₂ (ih _ ω) D₀))
  nd→seq' w ih (¬□E D D') 
   = cut (nd→seq' w ih D) 
      (¬□L i0 (λ D₀ → wk-seq wken (nd→seq' w ih 
        (D' (λ ω D'' → D₀ ω (proj₁ (ih _ ω) (wk-nd (wkto' ω) D'')))))))
  nd→seq' w ih (¬◇I ω D') = ¬◇R ω (λ D₀ → D' (proj₂ (ih _ ω) D₀))
  nd→seq' w ih (¬◇E D D') 
   = cut (nd→seq' w ih D)
      (¬◇L i0 (λ ω D₀ → wk-seq wken (nd→seq' w ih 
        (D' ω (λ D'' → D₀ (proj₁ (ih _ ω) (wk-nd (wkto' ω) D'')))))))

  seq→nd' : (w : W) → ((w' : W) → w ≺ w' → equivP w')
             → ∀{Γ A} → Γ ⇒ A [ w ] → Γ ⊢ A [ w ]
  seq→nd' w ih (hyp iN) = hyp iN
  seq→nd' w ih (⊃R D) = ⊃I (seq→nd' w ih D)
  seq→nd' w ih (⊃L iN D D') 
   = subst (⊃E (hyp iN) (seq→nd' w ih D)) (seq→nd' w ih D')
  seq→nd' w ih (□R D) = □I (λ ω → proj₂ (ih _ ω) (D ω))
  seq→nd' w ih (□L iN D) 
   = □E (hyp iN) 
      (λ D₀ → seq→nd' w ih (D (λ ω → proj₁ (ih _ ω) (D₀ ω))))
  seq→nd' w ih (◇R ω D) = ◇I ω (proj₂ (ih _ ω) D)
  seq→nd' w ih (◇L iN D) 
   = ◇E (hyp iN) 
      (λ ω D₀ → seq→nd' w ih (D ω (proj₁ (ih _ ω) D₀)))
  seq→nd' w ih (¬□R D) = ¬□I (λ ω D₀ → D ω (proj₁ (ih _ ω) D₀))
  seq→nd' w ih (¬□L iN D) 
   = ¬□E (hyp iN) 
      (λ D₀ → seq→nd' w ih (D (λ ω D' → D₀ ω (proj₂ (ih _ ω) D'))))
  seq→nd' w ih (¬◇R ω D) = ¬◇I ω (λ D₀ → D (proj₁ (ih _ ω) D₀))
  seq→nd' w ih (¬◇L iN D) 
   = ¬◇E (hyp iN)
      (λ ω D₀ → seq→nd' w ih (D ω (λ D' → D₀ (proj₂ (ih _ ω) D'))))

  nd→seq : ∀{Γ A w} → Γ ⊢ A [ w ] → Γ ⇒ A [ w ]
  nd→seq = proj₁
   (ind equivP (λ w ih → (λ D → nd→seq' _ ih D) ^ (λ D → seq→nd' _ ih D)) _)

  seq→nd : ∀{Γ A w} → Γ ⇒ A [ w ] → Γ ⊢ A [ w ]
  seq→nd = proj₂
   (ind equivP (λ w ih → (λ D → nd→seq' _ ih D) ^ (λ D → seq→nd' _ ih D)) _)
