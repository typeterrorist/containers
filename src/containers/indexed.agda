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

module containers.indexed where

private
  variable
    ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ ℓ₆ : Level

record Container (ℓ₂ ℓ₃ : Level) (I : UU ℓ₁) : UU (ℓ₁ ⊔ lsuc (ℓ₂ ⊔ ℓ₃)) where
  constructor _◁_◂_
  field
    Shape : I → UU ℓ₂
    Position : {i : I} → Shape i → UU ℓ₃
    reindex : {i : I} {s : Shape i} → Position s → I
open Container

⟦_⟧ : {I : UU ℓ₁}
    → Container ℓ₂ ℓ₃ I
    → (I → UU ℓ₄)
    → (I → UU (ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄))
⟦ S ◁ P ◂ r ⟧ X i = Σ (S i) (λ s → (p : P s) → X (r p))

map-⟦_⟧ : {I : UU ℓ₁} (C : Container ℓ₂ ℓ₃ I)
        → {X : I → UU ℓ₄} {Y : I → UU ℓ₅}
        → (∀ i → X i → Y i)
        → ∀ i → ⟦ C ⟧ X i → ⟦ C ⟧ Y i
map-⟦ S ◁ P ◂ r ⟧ f i = tot (λ s → f (r _) ∘_)

{- Compositions of containers -}

{- We define the sum of containers with positions
in the same universe to avoid having to raise
universe levels unnecessarily. -}
_⊕_ : {I : UU ℓ₁}
     → Container ℓ₂ ℓ₄ I
     → Container ℓ₃ ℓ₄ I
     → Container (ℓ₂ ⊔ ℓ₃) ℓ₄ I
Shape (C ⊕ D) i = Shape C i + Shape D i
Position (C ⊕ D) (inl s) = Position C s
Position (C ⊕ D) (inr t) = Position D t
reindex (C ⊕ D) {s = inl s} = reindex C {s = s}
reindex (C ⊕ D) {s = inr t} = reindex D {s = t}

equiv-⊕-+ : {I : UU ℓ₁}
           → {C : Container ℓ₂ ℓ₄ I}
           → {D : Container ℓ₃ ℓ₄ I}
           → {X : I → UU ℓ₅}
           → ∀ {i} → ⟦ C ⊕ D ⟧ X i ≃ ⟦ C ⟧ X i + ⟦ D ⟧ X i
pr1 equiv-⊕-+ ((inl s) , v) = inl (s , v)
pr1 equiv-⊕-+ ((inr t) , v) = inr (t , v)
pr2 equiv-⊕-+ =
  is-equiv-is-invertible
    (λ { (inl (s , v)) → (inl s , v) ; (inr (t , v)) → (inr t , v) })
    (λ { (inl (s , v)) → refl ; (inr (t , v)) → refl })
    (λ { ((inl s) , v) → refl ; ((inr t) , v) → refl })

_⊗_ : {I : UU ℓ₁}
     → Container ℓ₂ ℓ₃ I
     → Container ℓ₄ ℓ₅ I
     → Container (ℓ₂ ⊔ ℓ₄) (ℓ₃ ⊔ ℓ₅) I
Shape (C ⊗ D) i = Shape C i × Shape D i 
Position (C ⊗ D) (s , t) = Position C s + Position D t
reindex (C ⊗ D) (inl p) = reindex C p
reindex (C ⊗ D) (inr q) = reindex D q

equiv-⊗-× : {I : UU ℓ₁}
           → {C : Container ℓ₂ ℓ₃ I}
           → {D : Container ℓ₄ ℓ₅ I}
           → {X : I → UU ℓ₆}
           → ∀ {i} → ⟦ C ⊗ D ⟧ X i ≃ ⟦ C ⟧ X i × ⟦ D ⟧ X i
pr1 equiv-⊗-× ((s , t) , v) = ((s , v ∘ inl) , (t , v ∘ inr))
pr2 equiv-⊗-× =
  is-equiv-is-invertible
    (λ ((s , v) , (t , w)) → ((s , t) , λ { (inl p) → v p ; (inr q) → w q }))
    refl-htpy
    (λ ((s , t) , v) → eq-pair-Σ refl (eq-htpy (λ { (inl p) → refl ; (inr q) → refl })))

_⊚_ : {I : UU ℓ₁}
     → Container ℓ₂ ℓ₃ I
     → Container ℓ₄ ℓ₅ I
     → Container (ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄) (ℓ₃ ⊔ ℓ₅) I
Shape (C ⊚ D) = ⟦ C ⟧ (Shape D)
Position (C ⊚ D) (s , t) = Σ (Position C s) (Position D ∘ t)
reindex (C ⊚ D) (p , q) = reindex D q

equiv-⊚-∘ : {I : UU ℓ₁} {C : Container ℓ₂ ℓ₃ I}
           → {D : Container ℓ₄ ℓ₅ I}
           → {X : I → UU ℓ₆}
           → ∀ {i} → ⟦ C ⊚ D ⟧ X i ≃ ⟦ C ⟧ (⟦ D ⟧ X) i
pr1 equiv-⊚-∘ ((s , t) , v) = (s , λ p → (t p , curry v p))
pr2 equiv-⊚-∘ =
  is-equiv-is-invertible
    (λ (s , v) → ((s , pr1 ∘ v) , λ (p , q) → pr2 (v p) q))
    refl-htpy
    refl-htpy
