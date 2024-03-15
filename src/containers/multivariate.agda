open import foundation.cartesian-product-types
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.universe-levels

module containers.multivariate where

private
  variable
    ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ ℓ₆ ℓ₇ : Level

record Container (ℓ₂ ℓ₃ : Level) (I : UU ℓ₁) : UU (ℓ₁ ⊔ lsuc (ℓ₂ ⊔ ℓ₃)) where
  constructor _◁_
  field
    Shape : UU ℓ₂
    Position : Shape → I → UU ℓ₃
open Container

⟦_⟧ : {I : UU ℓ₁}
    → Container ℓ₂ ℓ₃ I
    → (I → UU ℓ₄)
    → UU (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄)
⟦ S ◁ P ⟧ X = Σ S (λ s → ∀ i → P s i → X i)

map-⟦_⟧ : {I : UU ℓ₁} (C : Container ℓ₂ ℓ₃ I)
        → {X : I → UU ℓ₄} {Y : I → UU ℓ₅}
        → (∀ i → X i → Y i)
        → ⟦ C ⟧ X → ⟦ C ⟧ Y
map-⟦ C ⟧ f = tot (λ s → map-Π (λ i → f i ∘_))

{- Compositions of containers -}

{- We define the sum of containers with positions
in the same universe to avoid having to raise
universe levels unnecessarily. -}
_⊕_ : {I : UU ℓ₁}
     → Container ℓ₂ ℓ₄ I
     → Container ℓ₃ ℓ₄ I
     → Container (ℓ₂ ⊔ ℓ₃) ℓ₄ I
Shape (C ⊕ D) = Shape C + Shape D
Position (C ⊕ D) (inl s) = Position C s
Position (C ⊕ D) (inr t) = Position D t

equiv-⊕-+ : {I : UU ℓ₁}
           → {C : Container ℓ₂ ℓ₄ I}
           → {D : Container ℓ₃ ℓ₄ I}
           → {X : I → UU ℓ₅}
           → ⟦ C ⊕ D ⟧ X ≃ ⟦ C ⟧ X + ⟦ D ⟧ X
pr1 equiv-⊕-+ (inl s , v) = inl (s , v)
pr1 equiv-⊕-+ (inr t , v) = inr (t , v)
pr2 equiv-⊕-+ =
  is-equiv-is-invertible
    (λ { (inl (s , v)) → (inl s , v) ; (inr (t , v)) → (inr t , v) })
    (λ { (inl (s , v)) → refl ; (inr (t , v)) → refl })
    (λ { ((inl s) , v) → refl ; ((inr t) , v) → refl })

_⊗_ : {I : UU ℓ₁}
     → Container ℓ₂ ℓ₃ I
     → Container ℓ₄ ℓ₅ I
     → Container (ℓ₂ ⊔ ℓ₄) (ℓ₃ ⊔ ℓ₅) I
Shape (C ⊗ D) = Shape C × Shape D
Position (C ⊗ D) (s , t) i = Position C s i + Position D t i

equiv-⊗-× : {I : UU ℓ₁}
           → {C : Container ℓ₂ ℓ₃ I}
           → {D : Container ℓ₄ ℓ₅ I}
           → {X : I → UU ℓ₆}
           → ⟦ C ⊗ D ⟧ X ≃ ⟦ C ⟧ X × ⟦ D ⟧ X
pr1 equiv-⊗-× ((s , t) , v) = ((s , (λ i → v i ∘ inl)) , (t , λ i → v i ∘ inr))
pr2 equiv-⊗-× =
  is-equiv-is-invertible
    (λ ((s , v) , (t , w)) → ((s , t) , λ i → λ { (inl p) → v i p ; (inr q) → w i q }))
    refl-htpy
    (λ ((s , t) , v) →
      eq-pair-Σ refl (eq-htpy (λ i → eq-htpy (λ { (inl p) → refl ; (inr q) → refl }))))

_⊚_ : {I : UU ℓ₁} {J : UU ℓ₂}
     → Container ℓ₃ ℓ₄ I
     → (I → Container ℓ₅ ℓ₆ J)
     → Container (ℓ₁ ⊔ ℓ₃ ⊔ ℓ₄ ⊔ ℓ₅) (ℓ₁ ⊔ ℓ₄ ⊔ ℓ₆) J
Shape (C ⊚ D) = ⟦ C ⟧ (Shape ∘ D)
Position (C ⊚ D) (s , t) j =
  Σ _ λ i → Σ (Position C s i) λ p → Position (D i) (t i p) j

equiv-⊚-∘ : {I : UU ℓ₁} {J : UU ℓ₂}
           → {C : Container ℓ₃ ℓ₄ I}
           → {D : I → Container ℓ₅ ℓ₆ J}
           → {X : J → UU ℓ₇}
           → ⟦ C ⊚ D ⟧ X ≃ ⟦ C ⟧ (λ i → ⟦ D i ⟧ X)
pr1 equiv-⊚-∘ ((s , t) , v) = (s , λ i p → (t i p , λ j q → v j (i , p , q)))
pr2 equiv-⊚-∘ =
  is-equiv-is-invertible
    (λ (s , v) → ((s , (λ i → pr1 ∘ v i)) , λ j (i , p , q) → pr2 (v i p) j q))
    refl-htpy
    refl-htpy
