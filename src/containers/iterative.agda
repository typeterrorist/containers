open import lists renaming (list to List)
open import lists.concatenation-lists renaming (concat-list to _++_)
open import foundation.universe-levels
open import foundation.dependent-pair-types
open import foundation.pi-decompositions
open import univalent-combinatorics.standard-finite-types
open import foundation.empty-types
open import foundation.unit-type
open import foundation.coproduct-types
open import foundation.function-types

import containers.multivariate as multivariate

module containers.iterative where
{-
 An iterative container is a representation of strictly positive
 elements of higher-order kinds. Univariate containers represent elements
 of Kind ∗ ⇒ ∗ which are strictly positive. Using iterative containers
 one can represent elements of more complex kinds such as (∗ ⇒ ∗) ⇒ (∗ ⇒ ∗).
-}



-- A data structure for canonical representations of kinds as rose trees:
data Kind : UU lzero where
    _⇒∗ : List Kind → Kind

-- Notation:

pattern ∗ = nil ⇒∗
pattern _⇒_⇒∗ k ks = cons k ks ⇒∗

infixr 100 _⇒_

-- The binary _⇒_ operator of kinds
_⇒_ : Kind → Kind → Kind
k ⇒ (k' ⇒∗) = (cons k k') ⇒∗

-- Realisation of a kind as an Agda type, replacing ∗ with UU i,
-- for some i : Level.
Type : ∀ i → Kind → UU (lsuc i)
Type i ∗ = UU i
Type i (k ⇒ ks ⇒∗) = Type i k → (Type i (ks ⇒∗))

-- "union" of kinds concatenates the argument lits
_∪_ : Kind → Kind → Kind
(ks ⇒∗) ∪ (ks' ⇒∗) = (ks ++ ks') ⇒∗

-- The following section introduces some convenince
-- functions for working with kinds.

-- Argument k is an index type for the arguments of k.
Argument : Kind → UU lzero
Argument ∗ = empty
Argument (k ⇒ ks ⇒∗) = Argument (ks ⇒∗) + unit 

-- The kind of a given argument of antother kind.
Argument-Kind : ∀ k → Argument k → Kind
Argument-Kind ∗ ()
Argument-Kind (_ ⇒ ks ⇒∗) (inl i) = Argument-Kind (ks ⇒∗) i
Argument-Kind (k ⇒ _ ⇒∗) (inr _) = k

-- Apply a realisation of a kind to an index of arguments.
apply : ∀ {i} k → Type i k → (∀ a → Type i (Argument-Kind k a)) → Type i ∗
apply ∗ X _ = X
apply (k ⇒ ks ⇒∗) F as = apply (ks ⇒∗) (F (as (inr star))) (as ∘ inl)

-- Create a realisation of a kind by abstraction.
abs : ∀ {i} k → ((∀ a → Type i (Argument-Kind k a)) → Type i ∗) → Type i k
abs ∗ f = f (λ{()})
abs (k ⇒ ks ⇒∗) f x = abs (ks ⇒∗) (λ as → f (λ { (inl a) → as a ; (inr _) → x}))

-- Partially apply a realisation of a union kind. 
partial-apply
   : ∀ {i} k k' → Type i (k ∪ k') → (∀ a → Type i (Argument-Kind k' a)) → Type i k
partial-apply ∗ (ks ⇒∗) t as = apply (ks ⇒∗) t as
partial-apply (k ⇒ ks ⇒∗) (ks' ⇒∗) t as X = partial-apply _ _ (t X) as

open multivariate.Container

record IterativeContainer i j (k : Kind) : UU (lsuc i ⊔ lsuc j) where
   inductive
   pattern
   constructor _⊲_
   field
       -- The Surface of an IterativeContainer represents a top
       -- level expression with variables decorated by the argument kinds
       -- for the container.
       Surface : multivariate.Container i j (Argument k)
       -- The Deeper structure gives arguments to variables of argument kinds
       -- which expect further arguments. The arguments of these are again
       -- unioned into the structure so that they can be used.
       -- Example : F ↦ X ↦ F (λ Y → X×Y)+X would have kind ((∗ ⇒ ∗) ⇒ ∗) ⇒ ∗ ⇒ ∗
       Deeper  : (a : Argument k)
                 (s : Shape Surface)
                 (p : Position Surface s a)
                 (a' : Argument (Argument-Kind k a))
                 → IterativeContainer i j ((Argument-Kind (Argument-Kind k a) a') ∪ k)

-- Realise a container of a given kind:

⟦_⟧ : ∀ {i k} → IterativeContainer i i k → Type i k
⟦_⟧ {k = k} ( S ⊲ D )
  = abs k (λ F → 
        Σ (Shape S) (λ s → ∀ a p 
                    → apply _ (F a) (λ a' → partial-apply _ _ (⟦ D a s p a' ⟧) F)))
