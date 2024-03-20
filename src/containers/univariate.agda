open import foundation.action-on-identifications-functions
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
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.univalence
open import foundation.universe-levels
open import foundation.whiskering-homotopies

module containers.univariate where

private
  variable
    ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ ℓ₆ : Level

record Container (ℓ₁ ℓ₂ : Level) : UU (lsuc (ℓ₁ ⊔ ℓ₂)) where
  constructor _◁_
  field
    Shape : UU ℓ₁
    Position : Shape → UU ℓ₂
open Container

Σ-Container : (ℓ₁ ℓ₂ : Level) → UU (lsuc (ℓ₁ ⊔ ℓ₂))
Σ-Container ℓ₁ ℓ₂ = Σ (UU ℓ₁) (λ Shape → Shape → UU ℓ₂)

Container≃Σ-Container : Container ℓ₁ ℓ₂ ≃ Σ-Container ℓ₁ ℓ₂
pr1 Container≃Σ-Container (S ◁ P) = (S , P)
pr2 Container≃Σ-Container =
  is-equiv-is-invertible
    (λ (S , P) → S ◁ P)
    refl-htpy
    refl-htpy

⟦_⟧ : Container ℓ₁ ℓ₂ → UU ℓ₃ → UU (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)
⟦ S ◁ P ⟧ X = Σ S (λ s → P s → X)

map-⟦_⟧ : (C : Container ℓ₁ ℓ₂)
        → {X : UU ℓ₃} {Y : UU ℓ₄}
        → (X → Y)
        → ⟦ C ⟧ X → ⟦ C ⟧ Y
map-⟦ C ⟧ f = tot (λ s → f ∘_)

{- Container morphisms -}

record Morphism (C : Container ℓ₁ ℓ₂) (D : Container ℓ₃ ℓ₄) :
    UU (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄) where
  field
    on-shapes : Shape C → Shape D
    on-positions : ∀ s → Position D (on-shapes s) → Position C s

Σ-Morphism : Container ℓ₁ ℓ₂
           → Container ℓ₃ ℓ₄
           → UU (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄)
Σ-Morphism (S ◁ P) (T ◁ Q) =
  Σ (S → T) λ f → ∀ s → Q (f s) → P s

Morphism≃Σ-Morphism : {C : Container ℓ₁ ℓ₂}
                    → {D : Container ℓ₃ ℓ₄}
                    → Morphism C D ≃ Σ-Morphism C D
pr1 Morphism≃Σ-Morphism
  record { on-shapes = f ; on-positions = σ } = (f , σ)
pr2 Morphism≃Σ-Morphism =
  is-equiv-is-invertible
    (λ (f , σ) → record { on-shapes = f ; on-positions = σ })
    refl-htpy
    refl-htpy

_⇒_ : Container ℓ₁ ℓ₂
    → Container ℓ₃ ℓ₄
    → UU (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄)
_⇒_ = Morphism

{- Equality on morphisms -}

record MorphismEquality {C : Container ℓ₁ ℓ₂} {D : Container ℓ₃ ℓ₄}
  (η γ : Morphism C D) : UU (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄) where
  field
    htpy-on-shapes : Morphism.on-shapes η ~ Morphism.on-shapes γ
    htpy-on-positions : ∀ s
                      → Morphism.on-positions η s
                      ~ Morphism.on-positions γ s ∘ tr (Position D) (htpy-on-shapes s)

Σ-MorphismEquality : {C : Container ℓ₁ ℓ₂} {D : Container ℓ₃ ℓ₄}
                   → Morphism C D
                   → Morphism C D
                   → UU (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄)
Σ-MorphismEquality {D = D} η γ =
  Σ (Morphism.on-shapes η ~ Morphism.on-shapes γ) (λ H →
    ∀ s → Morphism.on-positions η s
        ~ Morphism.on-positions γ s ∘ tr (Position D) (H s))

MorphismEquality≃Σ-MorphismEquality : {C : Container ℓ₁ ℓ₂} {D : Container ℓ₃ ℓ₄}
                                    → {η γ : Morphism C D}
                                    → MorphismEquality η γ
                                    ≃ Σ-MorphismEquality η γ
pr1 MorphismEquality≃Σ-MorphismEquality
  record { htpy-on-shapes = H ; htpy-on-positions = K } = (H , K)
pr2 MorphismEquality≃Σ-MorphismEquality =
  is-equiv-is-invertible
    (λ (H , K) → record { htpy-on-shapes = H ; htpy-on-positions = K })
    refl-htpy
    refl-htpy

Id≃MorphismEquality : {C : Container ℓ₁ ℓ₂} {D : Container ℓ₃ ℓ₄}
                    → {η γ : Morphism C D}
                    → (η ＝ γ)
                    ≃ MorphismEquality η γ
Id≃MorphismEquality {D = D} {η = η} {γ = γ} =
  inv-equiv MorphismEquality≃Σ-MorphismEquality ∘e
  extensionality-Σ
    (λ σ H → ∀ s → Morphism.on-positions η s ~ σ s ∘ tr (Position D) (H s))
    refl-htpy
    (λ s → refl-htpy)
    (λ f → equiv-funext)
    (λ σ →
      equiv-Π-equiv-family (λ s →
        equiv-funext) ∘e
      equiv-funext)
    (map-equiv Morphism≃Σ-Morphism γ) ∘e
  equiv-ap Morphism≃Σ-Morphism η γ

{- The natural transformation given by a morphism -}

transformation-⟦_⟧ : {C : Container ℓ₁ ℓ₂} {D : Container ℓ₃ ℓ₄}
                   → C ⇒ D
                   → {X : UU ℓ₅}
                   → ⟦ C ⟧ X → ⟦ D ⟧ X
transformation-⟦ η ⟧ (s , v)  =
  (Morphism.on-shapes η s ,
  v ∘ Morphism.on-positions η s)

is-nat-transformation-⟦_⟧ : {C : Container ℓ₁ ℓ₂} {D : Container ℓ₃ ℓ₄}
                          → (η : C ⇒ D)
                          → {X : UU ℓ₅} {Y : UU ℓ₆}
                          → (f : X → Y)
                          → transformation-⟦ η ⟧ ∘ map-⟦ C ⟧ f
                          ~ map-⟦ D ⟧ f ∘ transformation-⟦ η ⟧
is-nat-transformation-⟦ η ⟧ f = refl-htpy

{- The identity morphism -}

id-mor : (C : Container ℓ₁ ℓ₂)
       → C ⇒ C
Morphism.on-shapes (id-mor C) = id
Morphism.on-positions (id-mor C) s = id

htpy-id-transformation : {C : Container ℓ₁ ℓ₂} {X : UU ℓ₃}
                       → transformation-⟦ id-mor C ⟧ {X} ~ id
htpy-id-transformation = refl-htpy

{- Linear container morphisms -}

record LinearMorphism (C : Container ℓ₁ ℓ₂) (D : Container ℓ₃ ℓ₄) :
    UU (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄) where
  field
    on-shapes : Shape C → Shape D
    on-positions : ∀ s → Position D (on-shapes s) ≃ Position C s

Σ-LinearMorphism : Container ℓ₁ ℓ₂
                 → Container ℓ₃ ℓ₄
                 → UU (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄)
Σ-LinearMorphism (S ◁ P) (T ◁ Q) =
  Σ (S → T) λ f → ∀ s → Q (f s) ≃ P s

LinearMorphism≃Σ-LinearMorphism : {C : Container ℓ₁ ℓ₂}
                                → {D : Container ℓ₃ ℓ₄}
                                → LinearMorphism C D ≃ Σ-LinearMorphism C D
pr1 LinearMorphism≃Σ-LinearMorphism
  record { on-shapes = f ; on-positions = σ } = (f , σ)
pr2 LinearMorphism≃Σ-LinearMorphism =
  is-equiv-is-invertible
    (λ (f , σ) → record { on-shapes = f ; on-positions = σ })
    refl-htpy
    refl-htpy

_⇴_ : Container ℓ₁ ℓ₂ → Container ℓ₃ ℓ₄ → UU (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄)
_⇴_ = LinearMorphism

module _ {C : Container ℓ₁ ℓ₂} {D : Container ℓ₃ ℓ₄} where

  ⌊_⌋ : C ⇴ D → C ⇒ D
  Morphism.on-shapes ⌊ η ⌋ = LinearMorphism.on-shapes η
  Morphism.on-positions ⌊ η ⌋ s = map-equiv (LinearMorphism.on-positions η s)

  is-emb-⌊⌋ : is-emb ⌊_⌋
  is-emb-⌊⌋ =
    is-emb-comp
      (map-inv-equiv Morphism≃Σ-Morphism)
      (tot (λ f → map-Π (λ s → map-equiv))
        ∘ map-equiv LinearMorphism≃Σ-LinearMorphism)
      (is-emb-is-equiv
        (pr2 (inv-equiv Morphism≃Σ-Morphism)))
      (is-emb-comp
        (tot (λ f → map-Π (λ s → map-equiv)))
        (map-equiv LinearMorphism≃Σ-LinearMorphism)
        (is-emb-tot (λ f →
          is-emb-map-Π (λ s →
            is-emb-inclusion-subtype is-equiv-Prop)))
        (is-emb-is-equiv
          (pr2 LinearMorphism≃Σ-LinearMorphism)))

  emb-⌊_⌋ : (C ⇴ D) ↪ (C ⇒ D)
  pr1 emb-⌊_⌋ = ⌊_⌋
  pr2 emb-⌊_⌋ = is-emb-⌊⌋

{- Equivalence of containers -}

record Equivalence (C : Container ℓ₁ ℓ₂) (D : Container ℓ₃ ℓ₄) :
  UU (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄) where
  field
    on-shapes : Shape C ≃ Shape D
    on-positions : ∀ s → Position D (map-equiv on-shapes s) ≃ Position C s

Σ-Equivalence : Container ℓ₁ ℓ₂
              → Container ℓ₃ ℓ₄
              → UU (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄)
Σ-Equivalence (S ◁ P) (T ◁ Q) =
  Σ (S ≃ T) (λ e → ∀ s → Q (map-equiv e s) ≃ P s)

Equivalence≃Σ-Equivalence : {C : Container ℓ₁ ℓ₂} {D : Container ℓ₃ ℓ₄}
                          → Equivalence C D ≃ Σ-Equivalence C D
pr1 Equivalence≃Σ-Equivalence
  record { on-shapes = e ; on-positions = f } = (e , f)
pr2 Equivalence≃Σ-Equivalence =
  is-equiv-is-invertible
    (λ (e , f) → record { on-shapes = e ; on-positions = f })
    refl-htpy
    refl-htpy

Id≃Equivalence : {C D : Container ℓ₁ ℓ₂}
               → (C ＝ D)
               ≃ Equivalence C D
Id≃Equivalence {C = S ◁ P} {D = T ◁ Q} =
  inv-equiv Equivalence≃Σ-Equivalence ∘e
  extensionality-Σ
    (λ P' e → ∀ s → P' (map-equiv e s) ≃ P s)
    id-equiv
    (λ s → id-equiv)
    (λ S' → equiv-univalence)
    (λ P' →
      equiv-Π-equiv-family (λ s → equiv-univalence) ∘e
      equiv-funext ∘e
      (equiv-inv P P'))
    (T , Q) ∘e
  equiv-ap Container≃Σ-Container (S ◁ P) (T ◁ Q)

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

_⊛_ : Container ℓ₁ ℓ₂
    → Container ℓ₃ ℓ₄
    → Container (ℓ₁ ⊔ ℓ₃) (ℓ₂ ⊔ ℓ₄)
Shape (C ⊛ D) = Shape C × Shape D
Position (C ⊛ D) (s , t) = Position C s × Position D t
