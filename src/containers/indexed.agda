open import foundation.cartesian-product-types
open import foundation.coproduct-types
open import foundation.dependent-pair-types
  renaming (ind-Σ to uncurry; ev-pair to curry)
open import foundation.embeddings
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.transport-along-identifications
open import foundation.universe-levels

module containers.indexed where

import containers.doubly-indexed as doubly-indexed

private
  variable
    ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ ℓ₆ ℓ₇ : Level

Container : (ℓ₂ ℓ₃ : Level) → UU ℓ₁ → UU (ℓ₁ ⊔ lsuc ℓ₂ ⊔ lsuc ℓ₃)
Container ℓ₂ ℓ₃ I = doubly-indexed.Container ℓ₂ ℓ₃ I I

open module Container {ℓ₁ ℓ₂ ℓ₃ : Level} {I : UU ℓ₁}
  = doubly-indexed.Container {ℓ₃ = ℓ₂} {ℓ₄ = ℓ₃} {I = I} {J = I}
  public

module _ {I : UU ℓ₁} where

  ⟦_⟧ = doubly-indexed.⟦_⟧ {I = I} {J = I}
  map-⟦_⟧ = doubly-indexed.map-⟦_⟧ {I = I} {J = I}

{- Container morphisms -}

Morphism : {I : UU ℓ₁}
         → (C : Container ℓ₂ ℓ₃ I)
         → (D : Container ℓ₄ ℓ₅ I)
         → UU (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄ ⊔ ℓ₅)
Morphism = doubly-indexed.Morphism

module Morphism {ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ : Level} {I : UU ℓ₁}
  {C : Container ℓ₂ ℓ₃ I} {D : Container ℓ₄ ℓ₅ I}
  = doubly-indexed.Morphism {I = I} {J = I} {C = C} {D = D}

module _ {I : UU ℓ₁} where

  _⇒_ = doubly-indexed._⇒_ {I = I} {J = I}
  transformation-⟦_⟧ = doubly-indexed.transformation-⟦_⟧ {I = I} {J = I}
  is-nat-transformation-⟦_⟧ = doubly-indexed.is-nat-transformation-⟦_⟧ {I = I} {J = I}

  {- The identity morphism -}

  id-mor = doubly-indexed.id-mor {I = I} {J = I}
  htpy-id-transformation = doubly-indexed.htpy-id-transformation {I = I} {J = I}

{- Linear container morphisms -}

LinearMorphism : {I : UU ℓ₁}
               → (C : Container ℓ₂ ℓ₃ I)
               → (D : Container ℓ₄ ℓ₅ I)
               → UU (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄ ⊔ ℓ₅)
LinearMorphism = doubly-indexed.LinearMorphism

module LinearMorphism {ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ : Level} {I : UU ℓ₁}
  {C : Container ℓ₂ ℓ₃ I} {D : Container ℓ₄ ℓ₅ I}
  = doubly-indexed.LinearMorphism {I = I} {J = I} {C = C} {D = D}

module _ {I : UU ℓ₁} where

  _⇴_ = doubly-indexed._⇴_ {I = I} {J = I}
  ⌊_⌋ = doubly-indexed.⌊_⌋ {I = I} {J = I}

{- Compositions of containers -}

module _ {I : UU ℓ₁} where

  _⊕_ = doubly-indexed._⊕_ {I = I} {J = I}
  equiv-⊕-+ = doubly-indexed.equiv-⊕-+ {I = I} {J = I}
  _⊗_ = doubly-indexed._⊗_ {I = I} {J = I}
  equiv-⊗-× = doubly-indexed.equiv-⊗-× {I = I} {J = I}
  _⊚_ = doubly-indexed._⊚_ {I = I} {J = I} {K = I}
  equiv-⊚-∘ = doubly-indexed.equiv-⊚-∘ {I = I} {J = I} {K = I}
