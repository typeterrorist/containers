open import foundation.cartesian-product-types
open import foundation.coproduct-types
open import foundation.dependent-pair-types
  renaming (ind-Σ to uncurry; ev-pair to curry)
open import foundation.embeddings
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-dependent-function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.structure-identity-principle
open import foundation.univalence
open import foundation.universe-levels

module containers.doubly-indexed where

private
  variable
    ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ ℓ₆ ℓ₇ ℓ₈ : Level

record Container (ℓ₃ ℓ₄ : Level) (I : UU ℓ₁) (J : UU ℓ₂) :
    UU (ℓ₁ ⊔ ℓ₂ ⊔ lsuc ℓ₃ ⊔ lsuc ℓ₄) where
  constructor _◁_
  field
    Shape : I → UU ℓ₃
    Position : ∀ i → Shape i → J → UU ℓ₄
open Container

Σ-Container : (ℓ₃ ℓ₄ : Level) → UU ℓ₁ → UU ℓ₂
            → UU (ℓ₁ ⊔ ℓ₂ ⊔ lsuc ℓ₃ ⊔ lsuc ℓ₄)
Σ-Container ℓ₃ ℓ₄ I J  =
  Σ (I → UU ℓ₃) (λ Shape → ∀ i → Shape i → J → UU ℓ₄)

Container≃Σ-Container : {I : UU ℓ₁} {J : UU ℓ₂}
                      → Container ℓ₃ ℓ₄ I J ≃ Σ-Container ℓ₃ ℓ₄ I J
pr1 Container≃Σ-Container (S ◁ P) = (S , P)
pr2 Container≃Σ-Container =
  is-equiv-is-invertible
    (λ (S , P) → S ◁ P)
    refl-htpy
    refl-htpy

module _ {I : UU ℓ₁} {J : UU ℓ₂} where

  ⟦_⟧ : Container ℓ₃ ℓ₄ I J
      → (J → UU ℓ₅)
      → (I → UU (ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄ ⊔ ℓ₅)) 
  ⟦ S ◁ P ⟧ X i = Σ (S i) (λ s → ∀ j → (p : P i s j) → X j)

  map-⟦_⟧ : (C : Container ℓ₃ ℓ₄ I J)
          → {X : J → UU ℓ₅} {Y : J → UU ℓ₆}
          → (∀ j → X j → Y j)
          → ∀ i → ⟦ C ⟧ X i → ⟦ C ⟧ Y i
  map-⟦ S ◁ P ⟧ f i = tot (λ s v j → f j ∘ v j)

{- Container morphisms -}

record Morphism {I : UU ℓ₁} {J : UU ℓ₂}
  (C : Container ℓ₃ ℓ₄ I J) (D : Container ℓ₅ ℓ₆ I J) :
    UU (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄ ⊔ ℓ₅ ⊔ ℓ₆) where
  field
    on-shapes : ∀ i → Shape C i → Shape D i
    on-positions : ∀ i s j
                 → Position D i (on-shapes i s) j → Position C i s j

module _ {I : UU ℓ₁} {J : UU ℓ₂} where

  _⇒_ : Container ℓ₃ ℓ₄ I J
      → Container ℓ₅ ℓ₆ I J
      → UU (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄ ⊔ ℓ₅ ⊔ ℓ₆)
  _⇒_ = Morphism

  transformation-⟦_⟧ : {C : Container ℓ₃ ℓ₄ I J} {D : Container ℓ₅ ℓ₆ I J}
                     → C ⇒ D
                     → {X : J → UU ℓ₇}
                     → ∀ i → ⟦ C ⟧ X i → ⟦ D ⟧ X i
  transformation-⟦ η ⟧ i (s , v ) =
    (Morphism.on-shapes η i s ,
    λ j → v j ∘ Morphism.on-positions η i s j)

  is-nat-transformation-⟦_⟧ : {C : Container ℓ₃ ℓ₄ I J} {D : Container ℓ₅ ℓ₆ I J}
                            → (η : C ⇒ D)
                            → {X : J → UU ℓ₇} {Y : J → UU ℓ₈}
                            → (f : ∀ j → X j → Y j)
                            → ∀ i
                            → transformation-⟦ η ⟧ i ∘ map-⟦ C ⟧ f i
                            ~ map-⟦ D ⟧ f i ∘ transformation-⟦ η ⟧ {X} i
  is-nat-transformation-⟦ η ⟧ f i = refl-htpy

  {- The identity morphism -}

  id-mor : (C : Container ℓ₃ ℓ₄ I J)
         → C ⇒ C
  Morphism.on-shapes (id-mor C) i = id
  Morphism.on-positions (id-mor C) i s j = id

  htpy-id-transformation : {C : Container ℓ₃ ℓ₄ I J}
                         → {X : J → UU ℓ₅}
                         → ∀ {i} → transformation-⟦ id-mor C ⟧ {X} i ~ id
  htpy-id-transformation = refl-htpy

{- Linear container morphisms -}

record LinearMorphism {I : UU ℓ₁} {J : UU ℓ₂}
  (C : Container ℓ₃ ℓ₄ I J) (D : Container ℓ₅ ℓ₆ I J) :
    UU (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄ ⊔ ℓ₅ ⊔ ℓ₆) where
  field
    on-shapes : ∀ i → Shape C i → Shape D i
    on-positions : ∀ i s j
                 → Position D i (on-shapes i s) j ≃ Position C i s j

module _ {I : UU ℓ₁} {J : UU ℓ₂} where

  _⇴_ : Container ℓ₃ ℓ₄ I J
      → Container ℓ₅ ℓ₆ I J
      → UU (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄ ⊔ ℓ₅ ⊔ ℓ₆)
  _⇴_ = LinearMorphism

  ⌊_⌋ : {C : Container ℓ₃ ℓ₄ I J}
      → {D : Container ℓ₅ ℓ₆ I J}
      → C ⇴ D
      → C ⇒ D
  Morphism.on-shapes ⌊ η ⌋ = LinearMorphism.on-shapes η
  Morphism.on-positions ⌊ η ⌋ i s j = map-equiv (LinearMorphism.on-positions η i s j)

{- Equivalence of containers -}

record Equivalence {I : UU ℓ₁} {J : UU ℓ₂}
  (C : Container ℓ₃ ℓ₄ I J) (D : Container ℓ₅ ℓ₆ I J) :
    UU (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄ ⊔ ℓ₅ ⊔ ℓ₆) where
  field
    on-shapes : ∀ i → Shape C i ≃ Shape D i
    on-positions : ∀ i s j
                 → Position D i (map-equiv (on-shapes i) s) j ≃ Position C i s j

module _ {I : UU ℓ₁} {J : UU ℓ₂} where

  Σ-Equivalence : Container ℓ₃ ℓ₄ I J
                → Container ℓ₅ ℓ₆ I J
                → UU (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄ ⊔ ℓ₅ ⊔ ℓ₆)
  Σ-Equivalence (S ◁ P) (T ◁ Q) =
    Σ (∀ i → S i ≃ T i) (λ e →
      ∀ i (s : S i) → ∀ j → Q i (map-equiv (e i) s) j ≃ P i s j)

  Equivalence≃Σ-Equivalence : {C : Container ℓ₃ ℓ₄ I J}
                            → {D : Container ℓ₅ ℓ₆ I J}
                            → Equivalence C D ≃ Σ-Equivalence C D
  pr1 Equivalence≃Σ-Equivalence
    record { on-shapes = e ; on-positions = f } = (e , f)
  pr2 Equivalence≃Σ-Equivalence =
    is-equiv-is-invertible
      (λ (e , f) → record { on-shapes = e ; on-positions = f })
      refl-htpy
      refl-htpy

  Id≃Equivalence : {C D : Container ℓ₃ ℓ₄ I J}
                 → (C ＝ D)
                 ≃ Equivalence C D
  Id≃Equivalence {C = S ◁ P} {D = T ◁ Q} =
    inv-equiv Equivalence≃Σ-Equivalence ∘e
    extensionality-Σ
      (λ P' e → ∀ i (s : S i) → ∀ j → P' i (map-equiv (e i) s) j ≃ P i s j)
      (λ i → id-equiv)
      (λ i s j → id-equiv)
      (λ S' →
       equiv-Π-equiv-family (λ i → equiv-univalence) ∘e
       equiv-funext)
      (λ P' →
        equiv-Π-equiv-family (λ i →
          equiv-Π-equiv-family (λ s →
            equiv-Π-equiv-family (λ j →
              equiv-univalence) ∘e
            equiv-funext) ∘e
          equiv-funext) ∘e
        equiv-funext ∘e
        equiv-inv P P')
      (T , Q) ∘e
    equiv-ap Container≃Σ-Container (S ◁ P) (T ◁ Q)

{- Compositions of containers -}

module _ {I : UU ℓ₁} {J : UU ℓ₂} where

  {- We define the sum of containers with positions
  in the same universe to avoid having to raise
  universe levels unnecessarily. -}
  _⊕_ : Container ℓ₃ ℓ₅ I J
      → Container ℓ₄ ℓ₅ I J
      → Container (ℓ₃ ⊔ ℓ₄) ℓ₅ I J
  Shape (C ⊕ D) i = Shape C i + Shape D i
  Position (C ⊕ D) i (inl s) = Position C i s
  Position (C ⊕ D) i (inr t) = Position D i t

  equiv-⊕-+ : {C : Container ℓ₃ ℓ₅ I J}
            → {D : Container ℓ₄ ℓ₅ I J}
            → {X : J → UU ℓ₆}
            → ∀ {i} → ⟦ C ⊕ D ⟧ X i ≃ ⟦ C ⟧ X i + ⟦ D ⟧ X i
  pr1 equiv-⊕-+ ((inl s) , v) = inl (s , v)
  pr1 equiv-⊕-+ ((inr t) , v) = inr (t , v)
  pr2 equiv-⊕-+ =
    is-equiv-is-invertible
      (λ { (inl (s , v)) → (inl s , v) ; (inr (t , v)) → (inr t , v) })
      (λ { (inl (s , v)) → refl ; (inr (t , v)) → refl })
      (λ { ((inl s) , v) → refl ; ((inr t) , v) → refl })

  _⊗_ : Container ℓ₃ ℓ₄ I J
      → Container ℓ₅ ℓ₆ I J
      → Container (ℓ₃ ⊔ ℓ₅) (ℓ₄ ⊔ ℓ₆) I J
  Shape (C ⊗ D) i = Shape C i × Shape D i 
  Position (C ⊗ D) i (s , t) j = Position C i s j + Position D i t j

  equiv-⊗-× : {C : Container ℓ₃ ℓ₄ I J}
            → {D : Container ℓ₅ ℓ₆ I J}
            → {X : J → UU ℓ₇}
            → ∀ {i} → ⟦ C ⊗ D ⟧ X i ≃ ⟦ C ⟧ X i × ⟦ D ⟧ X i
  pr1 equiv-⊗-× ((s , t) , v) = ((s , λ j → v j ∘ inl) , (t , λ j → v j ∘ inr))
  pr2 equiv-⊗-× =
    is-equiv-is-invertible
      (λ ((s , v) , (t , w)) → ((s , t) , λ j → λ { (inl p) → v j p ; (inr q) → w j q }))
      refl-htpy
      (λ ((s , t) , v) →
        eq-pair-Σ
          refl
          (eq-htpy λ j →
            eq-htpy (λ { (inl p) → refl ; (inr q) → refl })))

module _ {I : UU ℓ₁} {J : UU ℓ₂} {K : UU ℓ₃} where

  _⊚_ : Container ℓ₄ ℓ₅ I J
      → Container ℓ₆ ℓ₇ J K
      → Container (ℓ₂ ⊔ ℓ₄ ⊔ ℓ₅ ⊔ ℓ₆) (ℓ₂ ⊔ ℓ₅ ⊔ ℓ₇) I K
  Shape (C ⊚ D) = ⟦ C ⟧ (Shape D)
  Position (C ⊚ D) i (s , t) k =
    Σ J (λ j →
      Σ (Position C i s j) λ p →
        Position D j (t j p) k)

  equiv-⊚-∘ : {C : Container ℓ₄ ℓ₅ I J}
            → {D : Container ℓ₆ ℓ₇ J K}
            → {X : K → UU ℓ₈}
            → ∀ {i} → ⟦ C ⊚ D ⟧ X i ≃ ⟦ C ⟧ (⟦ D ⟧ X) i
  pr1 equiv-⊚-∘ ((s , t) , v) = (s , λ j p → (t j p , λ k → curry (curry (v k) j) p))
  pr2 equiv-⊚-∘ =
    is-equiv-is-invertible
      (λ (s , v) → ((s , (λ j → pr1 ∘ v j)) , λ k (j , p , q) → pr2 (v j p) k q))
      refl-htpy
      refl-htpy

