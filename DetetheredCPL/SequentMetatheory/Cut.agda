-- Constructive Provability Logic 
-- De-tethered intuitionistic variant
-- Robert J. Simmons, Bernardo Toninho

-- This file has two problems. First, it doesn't pass the termination checker
-- (it should, but I don't have enough RAM). Second, it doesn't create an
-- interface file in any remotely reasonable amount of time (it does work 
-- eventually, though). Therefore, the only result in this file is duplicated 
-- in CutAxiom.agda as a postulate.

{-# OPTIONS --no-termination-check #-}

module DetetheredCPL.SequentMetatheory.Cut where
open import Prelude hiding (⊥)
open import Accessibility.Inductive 
open import Accessibility.IndexedList
open import DetetheredCPL.Core 
open import DetetheredCPL.SequentMetatheory.Core
open import DetetheredCPL.SequentMetatheory.IH
open import DetetheredCPL.SequentMetatheory.PreCut

module SEQUENT-CUT
   (UWF : UpwardsWellFounded)
   (dec≺ : (w w' : _) → Decidable (TRANS-UWF._≺*_ UWF w w')) where
   open TRANS-UWF UWF
   open ILIST UWF
   open CORE UWF 
   open SEQUENT-CORE UWF dec≺
   open SEQUENT-IH UWF dec≺
   open SEQUENT-PRE-CUT UWF dec≺

   x : Set
   x = {!!}

   cutP : (wc : W) → ((wc' : W) → wc ≺+ wc' → P wc') → ∀{Γ w A C}
            → Γ ⇒ A [ w ]
            → A at w :: Γ ⇒ C [ wc ]
            → Γ ⇒ C [ wc ]
   cutP wc ih {w = w} with dec≺ wc w
   cutP wc ih | Inr ω = λ _ → wk (⊆to/stenirrev ω (⊆to/refl _))
   cutP wc ih | Inl ω = cut* ω 
    where
     mutual
      -- Dispatch
      cut* : ∀{A Γ w C}
         → wc ≺* w
         → Γ ⇒ A [ w ]
         → A at w :: Γ ⇒ C [ wc ]
         → Γ ⇒ C [ wc ]
      cut* ≺*≡ D E = 
         cut ≺*≡ ⊆pr/refl (snd (→mP _ ih ⊆pr/refl D)) 
          (snd (→mP _ ih (extendP _ ih ⊆pr/refl D) E))
      cut* (≺*+ ω) D E = 
         cut (≺*+ ω) ⊆pr/refl (snd (P.→m (ih _ ω) ⊆pr/refl D))
          (snd (→mP _ ih (extendP _ ih ⊆pr/refl D) E))


      -- Primary lemma
      cut : ∀{A s₁ s₂ Γ w Δ C}
         → wc ≺* w
         → Δ ⊆ Γ pr wc
         → Δ / Γ ⇒ A [ w ]/ s₁
         → Δ / A at w :: Γ ⇒ C [ wc ]/ s₂
         → Γ ⇒ C [ wc ]

      -- Principal cuts
      cut ωc _ (hyp x) (hyp Z) = hyp x

      cut ωc subS (⊃R D₁) (⊃L Z E₁ E₂) =
         cut* ≺*≡
          (cut* ≺*≡ (cut ωc subS (⊃R D₁) E₁) (m→P _ ih (⊆pr/wken subS) D₁)) 
          (cut ωc (⊆pr/wken subS) (wkM wken (⊃R D₁)) (wkM exch E₂))

      cut ωc subS (⊃R D₁) (⊃L+ ωh Z E₁ E₂) = 
         cut* ωc DB
          (cut ωc (extendP _ ih subS DB') (wkM wken (⊃R D₁)) (wkM exch E₂))
       where
          DB = (P.cut (ih _ ωh) (P.subst (ih _ ωh) (⊆pr/≺+ ωh subS) E₁) 
           (P.m→ (ih _ ωh) (⊆pr/wken (⊆pr/≺+ ωh subS)) D₁))
          DB' = P.subst (ih _ ωh) (⊆pr/≺+' ωh subS) DB 

      cut ωc subS (◇R ω' D₁) (◇L ωh Z E₁) = 
         cut ωc subS (◇R ω' D₁) (E₁ ω' D₁)

      cut ωc subS (□R D₁) (□L ωh Z E₁) = 
         cut ωc subS (□R D₁) (E₁ D₁)


      -- Left commutative cuts
      cut ≺*≡ subS (⊃L x D₁ D₂) E = 
         ⊃L ≺*≡ x (m→P _ ih subS D₁) (cut ≺*≡ (⊆pr/wken subS) D₂ (wkM wkex E))

      cut ≺*≡ subS (⊃L+ ωh x D₁ D₂) E = 
         ⊃L (≺*+ ωh) x (P.subst (ih _ ωh) (⊆pr/≺+ ωh subS) D₁) 
          (cut ≺*≡ (extendP _ ih subS DB) D₂
           (wkM exch (decutMP _ ih (⊆pr/wken subS) DB' E)))
       where
         DB = P.⊃E' (ih _ ωh) (⊆pr/later' ωh subS x) D₁
         DB' = P.subst (ih _ ωh) (⊆pr/wkenirrev (≺+⊀ ωh) (⊆pr/≺+ ωh subS)) DB

      cut (≺*+ ωc) subS (⊃L x D₁ D₂) E = 
         ⊃L (≺*+ ωc) x (P.m→ (ih _ ωc) subW D₁) 
          (cut (≺*+ ωc) (extendP _ ih subS DB) D₂ 
           (wkM exch (decutMP _ ih (extendP _ ih subS DA) (wk wken DB') E)))
       where
         subW = ⊆pr/≺+ ωc subS
         subW' = ⊆pr/≺+' ωc subS
         DA = P.subst (ih _ ωc) subW' (P.m→ (ih _ ωc) subW (⊃L x D₁ D₂))
         DA0 = P.subst (ih _ ωc) subW' (P.m→ (ih _ ωc) (⊆pr/≺+ ωc subS) D₁)
         DB = P.⊃E' (ih _ ωc) (⊆pr/later' ωc subS x) DA0
         DB' = P.subst (ih _ ωc) subW DB

      cut (≺*+ ωc) subS (⊃L+ ωh x D₁ D₂) E = 
         ⊃L (≺*+ ωW) x (P.subst (ih _ ωW) subW D₁) 
          (cut (≺*+ ωc) (extendP _ ih subS DB) D₂
           (wkM exch (decutMP _ ih (extendP _ ih subS DA) 
            (wk (⊆to/wkenirrev (≺+⊀ ωh) (⊆to/refl _)) DB') E))) 
       where
         ωW = ≺+trans ωc ωh
         subW = ⊆pr/≺+ ωW subS
         subW' = ⊆pr/≺+' ωW subS
         DA = P.subst (ih _ ωc) (⊆pr/≺+' ωc subS)
            (P.m→ (ih _ ωc) (⊆pr/≺+ ωc subS) (⊃L+ ωh x D₁ D₂))
         DB = P.⊃E' (ih _ ωW) (⊆pr/later' ωW subS x) D₁
         DB' = P.subst (ih _ ωW) subW DB

      cut ωc subS (⊥L ωh x) E' = ⊥L (≺*trans ωc ωh) x

      cut ωc subS (◇L ωh x D₁) E' = ◇L (≺*trans ωc ωh) x 
         λ ω' D₀ → cut ωc subS 
          (D₁ ω' (P.subst (ih _ (≺*+trans ωc (≺*S' ωh ω')))
           (⊆pr/≺+' (≺*+trans ωc (≺*S' ωh ω')) subS) D₀)) E'

      cut ωc subS (□L ωh x D₁) E' = □L (≺*trans ωc ωh) x 
         λ D₀ → cut ωc subS (D₁ 
          λ ω' → P.subst (ih _ (≺*+trans ωc (≺*S' ωh ω')))
           (⊆pr/≺+' (≺*+trans ωc (≺*S' ωh ω')) subS) (D₀ ω')) E'


      -- Right commutative cuts
      cut ωc subS D (hyp (S x)) = hyp x

      cut ωc subS D (⊃R D₁) = 
         ⊃R (cut ωc (⊆pr/wken subS)
          (wkM (⊆to/wken* ωc (⊆to/refl _)) D) (wkM exch D₁))

      cut ωc subS D (⊃L (S x) D₁ D₂) = 
         ⊃L ≺*≡ x (cut ωc subS D D₁) 
          (cut ωc (⊆pr/wken subS) 
           (wkM (⊆to/wken* ωc (⊆to/refl _)) D) (wkM exch D₂))

      cut ≺*≡ subS D (⊃L+ ωh (S x) D₁ D₂) = 
         ⊃L (≺*+ ωh) x (P.subst (ih _ ωh) (⊆pr/≺+ ωh subS) D₁) 
          (cut ≺*≡ (extendP _ ih subS DB) 
           (decutMP _ ih subS DB' D) (wkM exch D₂))
       where
         DB = P.⊃E' (ih _ ωh) (⊆pr/later' ωh subS x) D₁ 
         DB' = P.subst (ih _ ωh) (⊆pr/≺+ ωh subS) DB

      cut (≺*+ ωc) subS D (⊃L+ ωh (S x) D₁ D₂) = 
         ⊃L (≺*+ ωh) x (P.subst (ih _ ωh) (⊆pr/≺+ ωh subS) D₁) 
          (cut (≺*+ ωc) (extendP _ ih subS DB) 
           (P.decutM (ih _ ωc) (⊆pr/≺+ ωc subS) DB' D) (wkM exch D₂))
        where
         DB = P.⊃E' (ih _ ωh) (⊆pr/later' ωh subS x) D₁
         DB' = P.subst (ih _ ωh) (⊆pr/≺+ ωh subS) DB

      cut ωc subS D (⊥L ωh (S x)) = ⊥L ωh x

      cut ωc subS D (◇R ω' D₁) = 
         ◇R ω' (P.subst (ih _ (≺+0 ω')) (⊆pr/≺+ (≺+0 ω') subS) D₁)

      cut ωc subS D (◇L ωh (S x) D₁) = ◇L ωh x
         λ ω' D₀ → cut ωc subS D 
          (D₁ ω' 
           (P.subst (ih _ (≺*S' ωh ω')) (⊆pr/≺+' (≺*S' ωh ω') subS) D₀))

      cut ωc subS D (□R D₁) = □R 
         λ ω' → P.subst (ih _ (≺+0 ω')) (⊆pr/≺+ (≺+0 ω') subS) (D₁ ω')

      cut ωc subS D (□L ωh (S x) D₁) = □L ωh x 
         λ D₀ → cut ωc subS D 
          (D₁ (λ ω' → 
           P.subst (ih _ (≺*S' ωh ω')) (⊆pr/≺+' (≺*S' ωh ω') subS) (D₀ ω')))
