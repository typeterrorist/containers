{-# OPTIONS --type-in-type #-}

{- using spine representation of types -}

open import Data.Product
open import Data.Unit
open import Data.Empty

data Con : Set
data Ty : Set where
  _⇒Set : Con → Ty

data Con where
  • : Con
  _▷_ : Con → Ty → Con

infixl 5 _▷_

variable A B C : Ty
variable Γ Δ : Con

_⇒_ : Ty → Ty → Ty
A ⇒ (Γ ⇒Set) = (Γ ▷ A) ⇒Set

data Var : Con → Ty → Set where
  zero : Var (Γ ▷ A) A
  suc : Var Γ A → Var (Γ ▷ B) A

record HCont-Set (Γ : Con) : Set 
data HCont-NE (Γ : Con) : Con → Set

data HCont-NF : Con → Ty → Set where
  lam : HCont-NF (Γ ▷ A) (Δ ⇒Set) → HCont-NF Γ ((Δ ▷ A) ⇒Set)
  ne : HCont-Set Γ → HCont-NF Γ (• ⇒Set)

record HCont-Set Γ  where
  inductive
  field
    S : Var Γ A → Set
    P : {x : Var Γ A}(s : S x) → Set
    R : {x : Var Γ (Δ ⇒Set)}{s : S x}(p : P s) → HCont-NE Γ Δ

data HCont-NE Γ where
  ε : HCont-NE Γ • 
  _,_ : HCont-NE Γ Δ → HCont-NF Γ A → HCont-NE Γ (Δ ▷ A)

HCont : Ty → Set
HCont A = HCont-NF • A


-- Semantics

⟦_⟧T : Ty → Set
⟦_⟧C : Con → Set

⟦ Γ ⇒Set ⟧T = ⟦ Γ ⟧C → Set
⟦ • ⟧C = ⊤
⟦ Γ ▷ A ⟧C = ⟦ Γ ⟧C × ⟦ A ⟧T

{-
appT : ⟦ A ⟧T → ⟦ dom A ⟧C → Set
appT {A = set} X tt = X
appT {A = A ⇒ B} f (β , a) = appT {A = B} (f a) β
-}
⟦_⟧v : Var Γ A → ⟦ Γ ⟧C → ⟦ A ⟧T
⟦ zero ⟧v (_ , a) = a
⟦ suc x ⟧v (γ , _) = ⟦ x ⟧v γ

-- record ⟦_⟧set (DD : HCont-Set Γ)(γ : ⟦ Γ ⟧C) : Set
⟦_⟧set : (DD : HCont-Set Γ)(γ : ⟦ Γ ⟧C) → Set
⟦_⟧ne : HCont-NE Γ Δ → ⟦ Γ ⟧C → ⟦ Δ ⟧C

⟦_⟧nf : HCont-NF Γ A → ⟦ Γ ⟧C → ⟦ A ⟧T
⟦ lam CC ⟧nf γ (δ , a) = ⟦ CC ⟧nf (γ , a) δ -- ⟦ CC ⟧nf (γ , a)
⟦ ne DD ⟧nf γ tt = ⟦ DD ⟧set γ -- ⟦ DD ⟧set γ

⟦_⟧set {Γ} record { S = S ; P = P ; R = R } γ =
  Σ[ s ∈ ({A : Ty}(x : Var Γ A) → S x) ]
    ({Δ : Con}{x : Var Γ (Δ ⇒Set)}{s : S x}(p : P s) → ⟦ x ⟧v γ (⟦ R p ⟧ne γ) )
{-
record ⟦_⟧set {Γ} CC γ where
  inductive
  open HCont-Set CC
  field
    s : (x : Var Γ A) → S x
    r : {x : Var Γ (Δ ⇒Set)}{s : S x}(p : P s) → ⟦ x ⟧v γ (⟦ R p ⟧ne γ) 
-}

⟦ ε ⟧ne γ = tt
⟦ CC* , CC ⟧ne γ = ⟦ CC* ⟧ne γ , ⟦ CC ⟧nf γ

{-
-- examples

H : (Set → Set) → (Set → Set)
H F A = A × F (F A)

TT : Ty
TT =  ((set ⇒ set)  ⇒ (set ⇒ set))
HC : HCont TT
HC = lam (lam (ne (record { S = S ; P = P ; R = R })))
  where Γ₀ : Con
        Γ₀ = • ▷ (set ⇒ set) ▷ set
        S : {A : Ty} → Var Γ₀ A → Set
        S zero = ⊤
        S (suc zero) = ⊤
        P : {A : Ty} {x : Var Γ₀ A} → S x → Set
        P {x = zero} tt = ⊤
        P {x = suc zero} tt = ⊤
        R-FA-S : {A : Ty} → Var Γ₀ A → Set
        R-FA-S zero = ⊤
        R-FA-S (suc zero) = ⊤
        R-FA-P :  {A : Ty} {x : Var Γ₀ A} → R-FA-S x → Set 
        R-FA-P {x = zero} tt = ⊤
        R-FA-P {x = suc zero} tt = ⊥
        R-FA-R :  {A : Ty} {x : Var Γ₀ A} {s : R-FA-S x} → R-FA-P s → HCont-NE Γ₀ A
        R-FA-R {x = zero} tt = ε
        R-FA-R {x = suc zero} ()
        R-FA-R {x = suc (suc ())} s
        R-FA : HCont-Set Γ₀
        R-FA = record { S = R-FA-S ; P = R-FA-P ; R = R-FA-R }            
        R-FFA-S : {A : Ty} → Var Γ₀ A → Set
        R-FFA-S zero = ⊤
        R-FFA-S (suc zero) = ⊤
        R-FFA-P :  {A : Ty} {x : Var Γ₀ A} → R-FFA-S x → Set 
        R-FFA-P {x = zero} tt = ⊥
        R-FFA-P {x = suc zero} tt = ⊤
        R-FFA-R :  {A : Ty} {x : Var Γ₀ A} {s : R-FFA-S x} → R-FFA-P s → HCont-NE Γ₀ A
        R-FFA-R {x = zero} ()
        R-FFA-R {x = suc zero} p = (ne R-FA) , ε
        R-FFA-R {x = suc (suc ())} s
        R-FFA : HCont-Set Γ₀
        R-FFA = record { S = R-FFA-S ; P = R-FFA-P ; R = R-FFA-R }  
        R : {A : Ty} {x : Var Γ₀ A} {s : S x} → P s → HCont-NE Γ₀ A
        R {x = zero} p = ε
        R {x = suc zero} p = (ne R-FFA) , ε

-}
