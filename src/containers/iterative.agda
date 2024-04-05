open import lists renaming (list to List)
open import foundation.universe-levels
open import foundation.dependent-pair-types
open import foundation.pi-decompositions

import containers.multivariate as multivariate

module containers.iterative where


data Index {i} {A : UU i} : List A → UU i where
   head-index : ∀ {a as} → Index (cons a as)
   tail-index : ∀ {a as} → Index as → Index (cons a as)

_!_ : ∀ {i} {A : UU i} (l : List A) → Index l → A
(cons a _) ! head-index = a
(cons _ as) ! (tail-index i) = as ! i

_++_ : ∀ {i} {A : UU i} → List A → List A → List A
nil ++ as = as
(cons a as) ++ as' = cons a (as ++ as')


data Kind : UU lzero where
    _⇒∗ : List Kind → Kind

pattern ∗ = nil ⇒∗

infixr 100 _⇒_

_⇒_ : Kind → Kind → Kind
k ⇒ (k' ⇒∗) = (cons k k') ⇒∗

functor : Kind
functor = ∗ ⇒ ∗

Type : ∀ i → Kind → UU (lsuc i)
Type i ∗ = UU i
Type i ((cons k ks)⇒∗) = Type i k → (Type i (ks ⇒∗))

_∪_ : Kind → Kind → Kind
(ks ⇒∗) ∪ (ks' ⇒∗) = (ks ++ ks') ⇒∗



Argument : Kind → UU lzero
Argument (ks ⇒∗) = Index ks

arg-kind : ∀ k → Argument k → Kind
arg-kind (ks ⇒∗) i = ks ! i

open multivariate.Container

record IterativeContainer i j (k : Kind) : UU (lsuc i ⊔ lsuc j) where
   inductive
   pattern
   constructor _⊲_
   field
       Surface : multivariate.Container i j (Argument k)
       Deeper  : (a : Argument k)
                 (s : Shape Surface)
                 (p : Position Surface s a)
                 (d' : Argument (arg-kind k a))
                 → IterativeContainer i j (arg-kind k a ∪ k)


⟦_⟧ : ∀ {i} k → IterativeContainer i i k → Type i k
⟦_⟧ ∗ ( S ⊲ D ) = (Shape S)
⟦_⟧ ((cons k ks) ⇒∗) ( S ⊲ D ) F = ? --Σ (Shape S) (λ s → ∀ a → (p : Position S s a) → ?)
