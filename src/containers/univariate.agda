open import foundation.cartesian-product-types
open import foundation.coproduct-types
open import foundation.dependent-pair-types
  renaming (ind-Σ to uncurry; ev-pair to curry)
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.universe-levels

module containers.univariate where

private
  variable
    ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level

record Container (ℓ₁ ℓ₂ : Level) : UU (lsuc (ℓ₁ ⊔ ℓ₂)) where
  constructor _◁_
  field
    Shape : UU ℓ₁
    Position : Shape → UU ℓ₂
open Container

⟦_⟧ : Container ℓ₁ ℓ₂ → UU ℓ₃ → UU (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)
⟦ S ◁ P ⟧ X = Σ S (λ s → P s → X)

map-⟦_⟧ : (C : Container ℓ₁ ℓ₂)
        → {X : UU ℓ₃} {Y : UU ℓ₄}
        → (X → Y)
        → ⟦ C ⟧ X → ⟦ C ⟧ Y
map-⟦ C ⟧ f = tot (λ s → f ∘_)

{- Compositions of containers -}

{- We define the sum of containers with positions
in the same universe to avoid having to raise
universe levels unnecessarily. -}
_⊕_ : Container ℓ₁ ℓ₃
     → Container ℓ₂ ℓ₃
     → Container (ℓ₁ ⊔ ℓ₂) ℓ₃
Shape (C ⊕ D) = Shape C + Shape D
Position (C ⊕ D) (inl s) = Position C s
Position (C ⊕ D) (inr t) = Position D t

equiv-⊕-+ : {C : Container ℓ₁ ℓ₃} {D : Container ℓ₂ ℓ₃}
           → {X : UU ℓ₄}
           → ⟦ C ⊕ D ⟧ X ≃ ⟦ C ⟧ X + ⟦ D ⟧ X
pr1 equiv-⊕-+ (inl s , v) = inl (s , v)
pr1 equiv-⊕-+ (inr t , v) = inr (t , v)
pr2 equiv-⊕-+ =
  is-equiv-is-invertible
    (λ { (inl (s , v)) → (inl s , v) ; (inr (t , v)) → (inr t , v) })
    (λ { (inl (s , v)) → refl ; (inr (t , v)) → refl })
    (λ { (inl s , v) → refl ; (inr t , v) → refl })

_⊗_ : Container ℓ₁ ℓ₂
     → Container ℓ₃ ℓ₄
     → Container (ℓ₁ ⊔ ℓ₃) (ℓ₂ ⊔ ℓ₄)
Shape (C ⊗ D) = Shape C × Shape D
Position (C ⊗ D) (s , t) = Position C s + Position D t

equiv-⊗-× : {C : Container ℓ₁ ℓ₃} {D : Container ℓ₂ ℓ₃}
           → {X : UU ℓ₄}
           → ⟦ C ⊗ D ⟧ X ≃ ⟦ C ⟧ X × ⟦ D ⟧ X
pr1 equiv-⊗-× ((s , t) , v) = ((s , v ∘ inl) , (t , v ∘ inr))
pr2 equiv-⊗-× =
  is-equiv-is-invertible
    (λ ((s , v) , (t , w)) → ((s , t) , λ { (inl p) → v p ; (inr q) → w q }))
    refl-htpy
    (λ ((s , t) , v) → eq-pair-Σ refl (eq-htpy (λ { (inl p) → refl ; (inr q) → refl })))

_⊚_ : Container ℓ₁ ℓ₂
     → Container ℓ₃ ℓ₄
     → Container (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃) (ℓ₂ ⊔ ℓ₄)
Shape (C ⊚ D) = ⟦ C ⟧ (Shape D)
Position (C ⊚ D) (s , t) = Σ (Position C s) (Position D ∘ t)

equiv-⊚-∘ : {C : Container ℓ₁ ℓ₃} {D : Container ℓ₂ ℓ₃}
           → {X : UU ℓ₄}
           → ⟦ C ⊚ D ⟧ X ≃ ⟦ C ⟧ (⟦ D ⟧ X)
pr1 equiv-⊚-∘ ((s , t) , v) = (s , λ p → (t p , curry v p))
pr2 equiv-⊚-∘ =
  is-equiv-is-invertible
    (λ (s , v) → ((s , pr1 ∘ v) , λ (p , q) → pr2 (v p) q))
    refl-htpy
    refl-htpy
