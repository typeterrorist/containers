open import foundation.cartesian-product-types
open import foundation.coproduct-types
open import foundation.dependent-pair-types
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
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.univalence
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

Σ-Container : (ℓ₂ ℓ₃ : Level) → UU ℓ₁ → UU (ℓ₁ ⊔ lsuc (ℓ₂ ⊔ ℓ₃))
Σ-Container ℓ₂ ℓ₃ I = Σ (UU ℓ₂) (λ Shape → Shape → I → UU ℓ₃)

Container≃Σ-Container : {I : UU ℓ₁}
                      → Container ℓ₂ ℓ₃ I ≃ Σ-Container ℓ₂ ℓ₃ I
pr1 Container≃Σ-Container (S ◁ P) = (S , P)
pr2 Container≃Σ-Container =
  is-equiv-is-invertible
    (λ (S , P) → S ◁ P)
    refl-htpy
    refl-htpy

module _ {I : UU ℓ₁} where

  ⟦_⟧ : Container ℓ₂ ℓ₃ I
      → (I → UU ℓ₄)
      → UU (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄)
  ⟦ S ◁ P ⟧ X = Σ S (λ s → ∀ i → P s i → X i)

  map-⟦_⟧ : (C : Container ℓ₂ ℓ₃ I)
          → {X : I → UU ℓ₄} {Y : I → UU ℓ₅}
          → (∀ i → X i → Y i)
          → ⟦ C ⟧ X → ⟦ C ⟧ Y
  map-⟦ C ⟧ f = tot (λ s → map-Π (λ i → f i ∘_))

{- Container morphisms -}

record Morphism {I : UU ℓ₁}
  (C : Container ℓ₂ ℓ₃ I) (D : Container ℓ₄ ℓ₅ I) :
    UU (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄ ⊔ ℓ₅) where
  field
    on-shapes : Shape C → Shape D
    on-positions : ∀ s i → Position D (on-shapes s) i → Position C s i

module _ {I : UU ℓ₁} where

  Σ-Morphism : Container ℓ₂ ℓ₃ I
             → Container ℓ₄ ℓ₅ I
             → UU (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄ ⊔ ℓ₅)
  Σ-Morphism (S ◁ P) (T ◁ Q) =
    Σ (S → T) λ f → ∀ s i → Q (f s) i → P s i

  Morphism≃Σ-Morphism : {C : Container ℓ₂ ℓ₃ I}
                      → {D : Container ℓ₄ ℓ₅ I}
                      → Morphism C D ≃ Σ-Morphism C D
  pr1 Morphism≃Σ-Morphism
    record { on-shapes = f ; on-positions = σ } = (f , σ)
  pr2 Morphism≃Σ-Morphism =
    is-equiv-is-invertible
      (λ (f , σ) → record { on-shapes = f ; on-positions = σ })
      refl-htpy
      refl-htpy

  _⇒_ : Container ℓ₂ ℓ₃ I → Container ℓ₄ ℓ₅ I
      → UU (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄ ⊔ ℓ₅)
  _⇒_ = Morphism

{- Equality on morphisms -}

record MorphismEquality {I : UU ℓ₁}
  {C : Container ℓ₂ ℓ₃ I} {D : Container ℓ₄ ℓ₅ I}
  (η γ : Morphism C D) : UU (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄ ⊔ ℓ₅) where
  field
    htpy-on-shapes : Morphism.on-shapes η ~ Morphism.on-shapes γ
    htpy-on-positions : ∀ s i
                      → Morphism.on-positions η s i
                      ~ Morphism.on-positions γ s i
                        ∘ tr (λ t → Position D t i) (htpy-on-shapes s)

module _ {I : UU ℓ₁}
  {C : Container ℓ₂ ℓ₃ I} {D : Container ℓ₄ ℓ₅ I}
  where

  Σ-MorphismEquality : Morphism C D
                     → Morphism C D
                     → UU (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄ ⊔ ℓ₅)
  Σ-MorphismEquality η γ =
    Σ (Morphism.on-shapes η ~ Morphism.on-shapes γ) (λ H →
      ∀ s i → Morphism.on-positions η s i
            ~ Morphism.on-positions γ s i ∘ tr (λ t → Position D t i) (H s))

  MorphismEquality≃Σ-MorphismEquality : {η γ : Morphism C D}
                                      → MorphismEquality η γ
                                      ≃ Σ-MorphismEquality η γ
  pr1 MorphismEquality≃Σ-MorphismEquality
    record { htpy-on-shapes = H ; htpy-on-positions = K } = (H , K)
  pr2 MorphismEquality≃Σ-MorphismEquality =
    is-equiv-is-invertible
      (λ (H , K) → record { htpy-on-shapes = H ; htpy-on-positions = K })
      refl-htpy
      refl-htpy

  Id≃MorphismEquality : {η γ : Morphism C D}
                      → (η ＝ γ)
                      ≃ MorphismEquality η γ
  Id≃MorphismEquality {η = η} {γ = γ} =
    inv-equiv MorphismEquality≃Σ-MorphismEquality ∘e
    extensionality-Σ
      (λ σ H → ∀ s i → Morphism.on-positions η s i ~ σ s i ∘ tr (λ t → Position D t i) (H s))
      refl-htpy
      (λ s i → refl-htpy)
      (λ f → equiv-funext)
      (λ σ →
        equiv-Π-equiv-family (λ s →
          equiv-Π-equiv-family (λ i →
            equiv-funext) ∘e
          equiv-funext) ∘e
        equiv-funext)
      (map-equiv Morphism≃Σ-Morphism γ) ∘e
    equiv-ap Morphism≃Σ-Morphism η γ

module _ {I : UU ℓ₁} where

  {- The natural transformation given by a morphism -}

  transformation-⟦_⟧ : {C : Container ℓ₂ ℓ₃ I} {D : Container ℓ₄ ℓ₅ I}
                     → C ⇒ D
                     → {X : I → UU ℓ₆}
                     → ⟦ C ⟧ X → ⟦ D ⟧ X
  transformation-⟦ η ⟧ (s , v ) =
    (Morphism.on-shapes η s ,
    λ i → v i ∘ Morphism.on-positions η s i)

  is-nat-transformation-⟦_⟧ : {C : Container ℓ₂ ℓ₃ I} {D : Container ℓ₄ ℓ₅ I}
                            → (η : C ⇒ D)
                            → {X : I → UU ℓ₆} {Y : I → UU ℓ₇}
                            → (f : ∀ i → X i → Y i)
                            → transformation-⟦ η ⟧ ∘ map-⟦ C ⟧ f
                            ~ map-⟦ D ⟧ f ∘ transformation-⟦ η ⟧
  is-nat-transformation-⟦ η ⟧ f = refl-htpy

  {- The identity morphism -}

  id-mor : (C : Container ℓ₂ ℓ₃ I)
         → C ⇒ C
  Morphism.on-shapes (id-mor C) = id
  Morphism.on-positions (id-mor C) s i = id

  htpy-id-transformation : {C : Container ℓ₂ ℓ₃ I} {X : I → UU ℓ₄}
                         → transformation-⟦ id-mor C ⟧ {X} ~ id
  htpy-id-transformation = refl-htpy

{- Linear container morphisms -}

record LinearMorphism {I : UU ℓ₁}
  (C : Container ℓ₂ ℓ₃ I) (D : Container ℓ₄ ℓ₅ I) :
    UU (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄ ⊔ ℓ₅) where
  field
    on-shapes : Shape C → Shape D
    on-positions : ∀ s i → Position D (on-shapes s) i ≃ Position C s i

module _ {I : UU ℓ₁} where

  Σ-LinearMorphism : Container ℓ₂ ℓ₃ I
                   → Container ℓ₄ ℓ₅ I
                   → UU (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄ ⊔ ℓ₅)
  Σ-LinearMorphism (S ◁ P) (T ◁ Q) =
    Σ (S → T) λ f → ∀ s i → Q (f s) i ≃ P s i

  LinearMorphism≃Σ-LinearMorphism : {C : Container ℓ₂ ℓ₃ I}
                                  → {D : Container ℓ₄ ℓ₅ I}
                                  → LinearMorphism C D ≃ Σ-LinearMorphism C D
  pr1 LinearMorphism≃Σ-LinearMorphism
    record { on-shapes = f ; on-positions = σ } = (f , σ)
  pr2 LinearMorphism≃Σ-LinearMorphism =
    is-equiv-is-invertible
      (λ (f , σ) → record { on-shapes = f ; on-positions = σ })
      refl-htpy
      refl-htpy

module _ {I : UU ℓ₁} where

  _⇴_ : Container ℓ₂ ℓ₃ I → Container ℓ₄ ℓ₅ I
      → UU (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄ ⊔ ℓ₅)
  _⇴_ = LinearMorphism

module _ {I : UU ℓ₁}
  {C : Container ℓ₂ ℓ₃ I} {D : Container ℓ₄ ℓ₅ I}
  where

  ⌊_⌋ : C ⇴ D → C ⇒ D
  Morphism.on-shapes ⌊ η ⌋ = LinearMorphism.on-shapes η
  Morphism.on-positions ⌊ η ⌋ s i = map-equiv (LinearMorphism.on-positions η s i)

  is-emb-⌊⌋ : is-emb ⌊_⌋
  is-emb-⌊⌋ =
    is-emb-comp
      (map-inv-equiv Morphism≃Σ-Morphism)
      (tot (λ f → map-Π (λ s → map-Π (λ i → map-equiv)))
        ∘ map-equiv LinearMorphism≃Σ-LinearMorphism)
      (is-emb-is-equiv
        (pr2 (inv-equiv Morphism≃Σ-Morphism)))
      (is-emb-comp
        (tot (λ f → map-Π (λ s → map-Π (λ i → map-equiv))))
        (map-equiv LinearMorphism≃Σ-LinearMorphism)
        (is-emb-tot (λ f →
          is-emb-map-Π (λ s →
            is-emb-map-Π (λ i →
              is-emb-inclusion-subtype is-equiv-Prop))))
        (is-emb-is-equiv
          (pr2 LinearMorphism≃Σ-LinearMorphism)))

  emb-⌊_⌋ : (C ⇴ D) ↪ (C ⇒ D)
  pr1 emb-⌊_⌋ = ⌊_⌋
  pr2 emb-⌊_⌋ = is-emb-⌊⌋

{- Equivalence of containers -}

record Equivalence {I : UU ℓ₁}
  (C : Container ℓ₂ ℓ₃ I) (D : Container ℓ₄ ℓ₅ I) :
    UU (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄ ⊔ ℓ₅) where
  field
    on-shapes : Shape C ≃ Shape D
    on-positions : ∀ s i → Position D (map-equiv on-shapes s) i ≃ Position C s i

module _ {I : UU ℓ₁} where

  Σ-Equivalence : Container ℓ₂ ℓ₃ I
                → Container ℓ₄ ℓ₅ I
                → UU (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄ ⊔ ℓ₅)
  Σ-Equivalence (S ◁ P) (T ◁ Q) =
    Σ (S ≃ T) (λ e → ∀ s i → Q (map-equiv e s) i ≃ P s i)

  Equivalence≃Σ-Equivalence : {C : Container ℓ₂ ℓ₃ I}
                            → {D : Container ℓ₄ ℓ₅ I}
                            → Equivalence C D ≃ Σ-Equivalence C D
  pr1 Equivalence≃Σ-Equivalence
    record { on-shapes = e ; on-positions = f } = (e , f)
  pr2 Equivalence≃Σ-Equivalence =
    is-equiv-is-invertible
      (λ (e , f) → record { on-shapes = e ; on-positions = f })
      refl-htpy
      refl-htpy

  Id≃Equivalence : {C D : Container ℓ₂ ℓ₃ I}
                 → (C ＝ D)
                 ≃ Equivalence C D
  Id≃Equivalence {C = S ◁ P} {D = T ◁ Q} =
    inv-equiv Equivalence≃Σ-Equivalence ∘e
    extensionality-Σ
      (λ P' e → ∀ s i → P' (map-equiv e s) i ≃ P s i)
      id-equiv
      (λ s i → id-equiv)
      (λ S' → equiv-univalence)
      (λ P' →
        equiv-Π-equiv-family (λ s →
          equiv-Π-equiv-family (λ i → equiv-univalence) ∘e
          equiv-funext)∘e
        equiv-funext ∘e
        (equiv-inv P P'))
      (T , Q) ∘e
    equiv-ap Container≃Σ-Container (S ◁ P) (T ◁ Q)

{- Compositions of containers -}

module _ {I : UU ℓ₁} where

{- We define the sum of containers with positions
in the same universe to avoid having to raise
universe levels unnecessarily. -}
  _⊕_ : Container ℓ₂ ℓ₄ I
      → Container ℓ₃ ℓ₄ I
      → Container (ℓ₂ ⊔ ℓ₃) ℓ₄ I
  Shape (C ⊕ D) = Shape C + Shape D
  Position (C ⊕ D) (inl s) = Position C s
  Position (C ⊕ D) (inr t) = Position D t

  equiv-⊕-+ : {C : Container ℓ₂ ℓ₄ I}
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

  _⊗_ : Container ℓ₂ ℓ₃ I
      → Container ℓ₄ ℓ₅ I
      → Container (ℓ₂ ⊔ ℓ₄) (ℓ₃ ⊔ ℓ₅) I
  Shape (C ⊗ D) = Shape C × Shape D
  Position (C ⊗ D) (s , t) i = Position C s i + Position D t i

  equiv-⊗-× : {C : Container ℓ₂ ℓ₃ I}
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

module _ {I : UU ℓ₁} {J : UU ℓ₂} where

  _⊚_ : Container ℓ₃ ℓ₄ I
      → (I → Container ℓ₅ ℓ₆ J)
      → Container (ℓ₁ ⊔ ℓ₃ ⊔ ℓ₄ ⊔ ℓ₅) (ℓ₁ ⊔ ℓ₄ ⊔ ℓ₆) J
  Shape (C ⊚ D) = ⟦ C ⟧ (Shape ∘ D)
  Position (C ⊚ D) (s , t) j =
    Σ _ λ i → Σ (Position C s i) λ p → Position (D i) (t i p) j

  equiv-⊚-∘ : {C : Container ℓ₃ ℓ₄ I}
            → {D : I → Container ℓ₅ ℓ₆ J}
            → {X : J → UU ℓ₇}
            → ⟦ C ⊚ D ⟧ X ≃ ⟦ C ⟧ (λ i → ⟦ D i ⟧ X)
  pr1 equiv-⊚-∘ ((s , t) , v) = (s , λ i p → (t i p , λ j q → v j (i , p , q)))
  pr2 equiv-⊚-∘ =
    is-equiv-is-invertible
      (λ (s , v) → ((s , (λ i → pr1 ∘ v i)) , λ j (i , p , q) → pr2 (v i p) j q))
      refl-htpy
      refl-htpy

module _ {I : UU ℓ₁} where

  _⊛_ : Container ℓ₂ ℓ₃ I
      → Container ℓ₄ ℓ₅ I
      → Container (ℓ₂ ⊔ ℓ₄) (ℓ₃ ⊔ ℓ₅) I
  Shape (C ⊛ D) = Shape C × Shape D
  Position (C ⊛ D) (s , t) i = Position C s i × Position D t i
