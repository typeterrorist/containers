open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.contractible-types
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.equality-cartesian-product-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-dependent-function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.raising-universe-levels
open import foundation.structure-identity-principle
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.unit-type
open import foundation.univalence
open import foundation.universe-levels
open import foundation.whiskering-homotopies

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

  htpy-map-⟦_⟧ : (C : Container ℓ₂ ℓ₃ I)
               → {X : I → UU ℓ₄} {Y : I → UU ℓ₅}
               → {f g : ∀ i → X i → Y i}
               → (∀ i → f i ~ g i)
               → map-⟦ C ⟧ f ~ map-⟦ C ⟧ g
  htpy-map-⟦ C ⟧ H (s , v) =
    eq-pair-eq-pr2 (eq-htpy (λ i → eq-htpy (H i ·r v i)))

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

δ : (ℓ₂ ℓ₃ : Level) {I : UU ℓ₁} → I → Container ℓ₂ (ℓ₁ ⊔ ℓ₃) I
Shape (δ ℓ₂ ℓ₃ i) = raise-unit ℓ₂
Position (δ ℓ₂ ℓ₃ i) _ i' = raise ℓ₃ (i ＝ i')

δ₀ : {I : UU ℓ₁} → I → Container lzero ℓ₁ I
Shape (δ₀ i) = unit
Position (δ₀ i) _ i' = i ＝ i'

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

{- Multivariate containers are a special case of indexed containers -}

import containers.indexed as indexed

module _ {I : UU ℓ₁} where

  to-indexed : Container ℓ₂ ℓ₃ I ≃ indexed.Container ℓ₂ ℓ₃ unit I
  pr1 to-indexed (S ◁ P) = (λ _ → S) indexed.◁ (λ _ → P)
  pr2 to-indexed =
    is-equiv-is-invertible
      (λ (S indexed.◁ P) → S star ◁ P star)
      refl-htpy
      refl-htpy

{- Least fixpoint -}

data μShape {I : UU ℓ₁} (C : Container ℓ₂ ℓ₃ (I + unit)) : UU (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃) where
  sup : (s : Shape C) → (Position C s (inr star) → μShape C) → μShape C

desup : {I : UU ℓ₁} (C : Container ℓ₂ ℓ₃ (I + unit))
      → μShape C → Σ (Shape C) (λ s → Position C s (inr star) → μShape C)
desup C (sup s v) = (s , v)

data μPosition {I : UU ℓ₁} (C : Container ℓ₂ ℓ₃ (I + unit))
  (s : μShape C) (i : I) :
  UU (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃) where
  supₗ : Position C (pr1 (desup C s)) (inl i) → μPosition C s i
  supᵣ : (p : Position C (pr1 (desup C s)) (inr star))
       → μPosition C (pr2 (desup C s) p) i → μPosition C s i

ind-μPosition : {I : UU ℓ₁} {C : Container ℓ₂ ℓ₃ (I + unit)}
              → {s : μShape C} {i : I}
              → (Z : μPosition C s i → UU ℓ₄)
              → ((p : Position C (pr1 (desup C s)) (inl i)) → Z (supₗ p))
              → ((p : Position C (pr1 (desup C s)) (inr star))
                → (q : μPosition C (pr2 (desup C s) p) i)
                → Z (supᵣ p q))
              → (p : μPosition C s i) → Z p
ind-μPosition Z f g (supₗ p) = f p
ind-μPosition Z f g (supᵣ p q) = g p q

{-μPosition' : {I : UU ℓ₁} (C : Container ℓ₂ ℓ₃ (I + unit))
           → (s : μShape C) (i : I)
           → UU (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)
μPosition' C (sup s t) i =
  Position C s (inl i) + Σ (Position C s (inr star)) (λ p → μPosition' C (t p) i)

μPosition≃μPosition' : {I : UU ℓ₁} {C : Container ℓ₂ ℓ₃ (I + unit)}
                     → (s : μShape C) (i : I)
                     → μPosition C s i
                     ≃ μPosition' C s i
pr1 (μPosition≃μPosition' (sup s t) i) (supₗ p) = inl p
pr1 (μPosition≃μPosition' (sup s t) i) (supᵣ p q) = inr (p , map-equiv (μPosition≃μPosition' (t p) i) q)
pr2 (μPosition≃μPosition' (sup s t) i) =
  is-equiv-is-invertible
    {!!}
    {!!}
    {!!}-}
  

module _ {I : UU ℓ₁} where

  μ : Container ℓ₂ ℓ₃ (I + unit) → Container (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃) (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃) I
  μ C = μShape C ◁ μPosition C

  _,,_ : (I → UU ℓ₁)
       → UU ℓ₁
       → I + unit → UU ℓ₁
  X ,, Y = ind-coprod _ X (λ _ → Y)
  {-(X ,, Y) (inl i) = X i
  (X ,, Y) (inr _) = Y-}

  foo : (X : I → UU ℓ₁)
      → (Y : UU ℓ₁)
      → (X ,, Y) ＝ ind-coprod _ X (λ _ → Y)
  foo X Y = refl

  id,, : {X : I → UU ℓ₁}
       → {Y Z : UU ℓ₁}
       → (Y → Z)
       → ∀ i → (X ,, Y) i → (X ,, Z) i
  id,, f = ind-coprod _ (λ i → id) (λ _ → f)
  {-id,, f (inl i) = id
  id,, f (inr _) = f-}

  id,,~ : {X : I → UU ℓ₁}
        → {Y Z : UU ℓ₁}
        → {f g : Y → Z}
        → f ~ g
        → ∀ i → (id,, {X = X} f) i ~ (id,, g) i
  id,,~ H = ind-coprod _ (λ i → refl-htpy) (λ _ → H)
  {-id,,~ H (inl i) = refl-htpy
  id,,~ H (inr _) = H-}


{- We show initiality for containers and families in
the same universe to avoid having to raise universe
levels unnecessarily. -}
module _ {I : UU ℓ₁} (C : Container ℓ₁ ℓ₁ (I + unit))
  (X : I → UU ℓ₁) where

  alg-map-μ : ⟦ C ⟧ (X ,, ⟦ μ C ⟧ X) → ⟦ μ C ⟧ X -- 1 + A × List A → List A
  alg-map-μ (s , v) =
    (sup s (pr1 ∘ v (inr star)) ,
    (λ i →
      ind-μPosition _
        (v (inl i))
        (λ p q → pr2 (v (inr star) p) i q)))
      {-λ { (supₗ p) → v (inl i) p ;
          (supᵣ p q) → pr2 (v (inr star) p) i q }))-}

  coalg-map-μ : ⟦ μ C ⟧ X → ⟦ C ⟧ (X ,, ⟦ μ C ⟧ X)
  coalg-map-μ (sup s t , v) =
    (s ,
    ind-coprod _
      (λ i p → v i (supₗ p))
      (λ _ p → (t p , λ i q → v i (supᵣ p q))))
    {-λ { (inl i) p → v i (supₗ p) ;
        (inr star) p → (t p , λ i q → v i (supᵣ p q)) })-}

  alg-≃-μ : ⟦ C ⟧ (X ,, ⟦ μ C ⟧ X) ≃ ⟦ μ C ⟧ X
  pr1 alg-≃-μ = alg-map-μ
  pr2 alg-≃-μ =
    is-equiv-is-invertible
      coalg-map-μ
      (λ { (sup s t , v) →
             eq-pair-eq-pr2
               (eq-htpy (λ i →
                 eq-htpy
                   (ind-μPosition _ refl-htpy (λ p → refl-htpy)))) })
                   {-(λ { (supₗ p) → refl ; (supᵣ p q) → refl }))) })-}
      (λ (s , v) →
           eq-pair-eq-pr2
             (eq-htpy
               (ind-coprod _ refl-htpy refl-htpy)))
               {-(λ { (inl i) → refl ; (inr star) → refl })))-}

module _ {I : UU ℓ₁} (C : Container ℓ₁ ℓ₁ (I + unit))
  (X : I → UU ℓ₁)
  {Y : UU ℓ₁} (f : ⟦ C ⟧ (X ,, Y) → Y) where

  rec-μ : ⟦ μ C ⟧ X → Y
  rec-μ (s , v) = curried-rec-μ s v
    where
      curried-rec-μ : (s : μShape C)
                    → (∀ i → μPosition C s i → X i)
                    → Y
      curried-rec-μ (sup s t) v =
        f (s ,
          ind-coprod _
            (λ i p → v i (supₗ p))
            (λ _ p → curried-rec-μ (t p) (λ i q → v i (supᵣ p q))))
          {-λ { (inl i) p → v i (supₗ p) ;
           (inr star) p → curried-rec-μ (t p) (λ i q → v i (supᵣ p q)) })-}

  is-alg-hom-rec-μ : (f ∘ map-⟦ C ⟧ (id,, rec-μ))
                   ~ (rec-μ ∘ alg-map-μ C X)
  is-alg-hom-rec-μ (s , v) =
    ap f
       (eq-pair-eq-pr2
         (eq-htpy (ind-coprod _ (λ i → refl) (λ _ → refl))))
                  --(λ { (inl i) → refl ; (inr star) → refl })))

  is-unique-rec-μ : (r : ⟦ μ C ⟧ X → Y)
                  → (f ∘ map-⟦ C ⟧ (id,, r)) ~ (r ∘ alg-map-μ C X)
                  → rec-μ ~ r
  is-unique-rec-μ r H (s , v) = curried-is-unique-rec-μ s v
    where
      curried-is-unique-rec-μ : (s : μShape C)
                              → (v : ∀ i → μPosition C s i → X i)
                              → rec-μ (s , v) ＝ r (s , v)
      curried-is-unique-rec-μ (sup s t) v =
        ap (λ v' → f (s , v'))
           (eq-htpy
             (ind-coprod _
               refl-htpy
               (λ _ → eq-htpy (λ p → curried-is-unique-rec-μ (t p) (λ i q → v i (supᵣ p q) ))))) ∙
             {-(λ { (inl i) → refl ;
                  (inr star) → eq-htpy (λ p → curried-is-unique-rec-μ (t p) (λ i q → v i (supᵣ p q) )) })) ∙-}
        H (coalg-map-μ C X (sup s t , v)) ∙
        ap r
           (eq-pair-eq-pr2
             (eq-htpy (λ i →
               eq-htpy
                 (ind-μPosition _ refl-htpy (λ p → refl-htpy)))))
                 --(λ { (supₗ p) → refl ; (supᵣ p q) → refl }))))

  Id-alg-hom : {(r , H) (r' , H') :
                   Σ (⟦ μ C ⟧ X → Y) (λ r → (f ∘ map-⟦ C ⟧ (id,, r)) ~ (r ∘ alg-map-μ C X))}
             → ((r , H) ＝ (r' , H'))
             ≃ Σ (r ~ r') (λ α →
                 H ∙h (α ·r alg-map-μ C X) ~
                 (f ·l htpy-map-⟦ C ⟧ (id,,~ α)) ∙h H')
  Id-alg-hom {(r , H)} {(r' , H')} =
    extensionality-Σ
      (λ H' α →
        H ∙h (α ·r alg-map-μ C X) ~
        (f ·l htpy-map-⟦ C ⟧ (id,,~ α)) ∙h H')
      refl-htpy
      (λ (s , v) →
        right-unit ∙
        ap (λ p → ap f (eq-pair-eq-pr2 p) ∙ H (s , v))
           (inv (eq-htpy-refl-htpy (λ i → id,, r i ∘ v i)) ∙
           ap eq-htpy
              (eq-htpy
                (λ { (inl i) → inv (eq-htpy-refl-htpy (v (inl i))) ;
                     (inr star) → inv (eq-htpy-refl-htpy (r ∘ v (inr star))) }))))
      (λ r' → equiv-funext)
      (λ H' →
        equiv-concat-htpy (λ (s , v) → right-unit) _ ∘e
        equiv-concat-htpy' _ (λ (s , v) →
          ap (λ p → ap f (eq-pair-eq-pr2 p) ∙ H' (s , v))
             (inv (eq-htpy-refl-htpy (λ i → id,, r i ∘ v i)) ∙
             ap eq-htpy
                (eq-htpy
                  (λ { (inl i) → inv (eq-htpy-refl-htpy (v (inl i))) ;
                       (inr star) → inv (eq-htpy-refl-htpy (r ∘ v (inr star))) })))) ∘e
        equiv-funext)
      (r' , H')

  is-initial-alg-μ : is-contr (Σ (⟦ μ C ⟧ X → Y) (λ r →
                                 (f ∘ map-⟦ C ⟧ (id,, r)) ~ (r ∘ alg-map-μ C X)))
  pr1 is-initial-alg-μ = (rec-μ , is-alg-hom-rec-μ)
  pr2 is-initial-alg-μ (r , H) =
    map-inv-equiv
      Id-alg-hom
      (is-unique-rec-μ r H ,
      (λ (s , v) →

    equational-reasoning
      (is-alg-hom-rec-μ (s , v) ∙ (is-unique-rec-μ r H ·r alg-map-μ C X) (s , v))
      ＝ ap f (eq-pair-eq-pr2
               (eq-htpy (ind-coprod _ refl-htpy refl-htpy))) ∙
        (is-unique-rec-μ r H ·r alg-map-μ C X) (s , v)                           by refl
      ＝ ap f (eq-pair-eq-pr2
               (eq-htpy (ind-coprod _ refl-htpy refl-htpy))) ∙
        (is-unique-rec-μ r H (alg-map-μ C X (s , v)))                           by refl
      ＝ ap f (eq-pair-eq-pr2
               (eq-htpy (ind-coprod _ refl-htpy refl-htpy))) ∙
        (ap (λ v' → f (s , v'))
           (eq-htpy
             (ind-coprod _
               refl-htpy
               (λ _ → eq-htpy (λ p → is-unique-rec-μ r H (pr1 (v (inr star) p) , (λ i q → pr2 (v (inr star) p) i q)))))) ∙
        H (coalg-map-μ C X (alg-map-μ C X (s , v))) ∙
        ap r
           (eq-pair-eq-pr2
             (eq-htpy (λ i →
               eq-htpy
                 (ind-μPosition _ refl-htpy (λ p → refl-htpy)))))) by refl
      ＝ ap f (eq-pair-eq-pr2
               (eq-htpy (ind-coprod _ refl-htpy refl-htpy))) ∙
        (ap (λ v' → f (s , v'))
           (eq-htpy
             (ind-coprod _
               refl-htpy
               (λ _ → eq-htpy (λ p → is-unique-rec-μ r H (pr1 (v (inr star) p) , (λ i q → pr2 (v (inr star) p) i q)))))) ∙
        H (coalg-map-μ C X (alg-map-μ C X (s , v))) ∙
        ap r (eq-pair-eq-pr2 refl)) by ap (λ α → ap f (eq-pair-eq-pr2
                                                         (eq-htpy (ind-coprod _ refl-htpy refl-htpy))) ∙ ((ap (λ v' → f (s , v'))
                                                                                      (eq-htpy
                                                                                        (ind-coprod _
                                                                                          refl-htpy
                                                                                          (λ _ → eq-htpy (λ p → is-unique-rec-μ r H (pr1 (v (inr star) p) , (λ i q → pr2 (v (inr star) p) i q)))))) ∙
                                                                                   H (coalg-map-μ C X (alg-map-μ C X (s , v)))) ∙ ap r (eq-pair-eq-pr2 α)))
                                                                                                  (ap eq-htpy (eq-htpy (λ i →
                                                                                                    ap eq-htpy (eq-htpy
                                                                                                      (ind-μPosition _ refl-htpy (λ p → refl-htpy))) ∙
                                                                                                    eq-htpy-refl-htpy _)) ∙
                                                                                                  eq-htpy-refl-htpy _)
      ＝ ap f (eq-pair-eq-pr2
               (eq-htpy (ind-coprod _ refl-htpy refl-htpy))) ∙
        (ap (λ v' → f (s , v'))
           (eq-htpy
             (ind-coprod _
               refl-htpy
               (λ _ → eq-htpy (λ p → is-unique-rec-μ r H (pr1 (v (inr star) p) , (λ i q → pr2 (v (inr star) p) i q)))))) ∙
        H (coalg-map-μ C X (alg-map-μ C X (s , v)))) by ap (ap f (eq-pair-eq-pr2
                                               (eq-htpy (ind-coprod _ refl-htpy refl-htpy))) ∙_)
                                                          right-unit
      ＝ ap f (eq-pair-eq-pr2
               (eq-htpy (ind-coprod _ refl-htpy refl-htpy))) ∙
        ap (λ v' → f (s , v'))
           (eq-htpy
             (ind-coprod _
               refl-htpy
               (λ _ → eq-htpy (λ p → is-unique-rec-μ r H (pr1 (v (inr star) p) , (λ i q → pr2 (v (inr star) p) i q)))))) ∙
        H (coalg-map-μ C X (alg-map-μ C X (s , v))) by inv (assoc _ _ _)
      ＝ ap (λ v' → f (s , v'))
               (eq-htpy (ind-coprod _ refl-htpy refl-htpy)) ∙
        ap (λ v' → f (s , v'))
           (eq-htpy
             (ind-coprod _
               refl-htpy
               (λ _ → eq-htpy (λ p → is-unique-rec-μ r H (pr1 (v (inr star) p) , (λ i q → pr2 (v (inr star) p) i q)))))) ∙
        H (coalg-map-μ C X (alg-map-μ C X (s , v))) by ap (λ α → α ∙ ap (λ v' → f (s , v'))
                                 (eq-htpy
                                   (ind-coprod _
                                     refl-htpy
                                     (λ _ → eq-htpy (λ p → is-unique-rec-μ r H (pr1 (v (inr star) p) , (λ i q → pr2 (v (inr star) p) i q)))))) ∙
                              H (coalg-map-μ C X (alg-map-μ C X (s , v)))) (inv (ap-comp f (λ v' → (s , v')) _))
      ＝ ap (λ v' → f (s , v'))
          (eq-htpy (ind-coprod _ refl-htpy refl-htpy) ∙
          eq-htpy
             (ind-coprod _
               refl-htpy
               (λ _ → eq-htpy (λ p → is-unique-rec-μ r H (pr1 (v (inr star) p) , (λ i q → pr2 (v (inr star) p) i q)))))) ∙
        H (coalg-map-μ C X (alg-map-μ C X (s , v))) by ap (_∙ H (coalg-map-μ C X (alg-map-μ C X (s , v))))
                                                          (inv (ap-concat (λ v' → f (s , v')) _ _))
      ＝ ap (λ v' → f (s , v'))
               (eq-htpy (λ i → eq-htpy ((id,,~ (is-unique-rec-μ r H)) i ·r v i))) ∙
         H (s , v) by {!!}
      ＝ ap f (eq-pair-eq-pr2
               (eq-htpy (λ i → eq-htpy ((id,,~ (is-unique-rec-μ r H)) i ·r v i)))) ∙
         H (s , v) by ap (_∙ H (s , v)) (ap-comp f (λ v' → (s , v')) _)
      ＝ ap f (htpy-map-⟦ C ⟧ (id,,~ (is-unique-rec-μ r H)) (s , v)) ∙ H (s , v) by refl
      ＝ (f ·l htpy-map-⟦ C ⟧ (id,,~ (is-unique-rec-μ r H))) (s , v) ∙ H (s , v) by refl
    ))


