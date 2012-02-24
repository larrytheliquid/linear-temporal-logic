open import FRP.JS.True renaming ( ⊥ to ⊥₀ ; ⊤ to ⊤₀ )

module LTL

  (Time    : Set)
  (initial : Time)
  (_≤_     : Time → Time → Set)
  -- (reflex  : Reflexive _≤_)
  -- (transit : Transitive _≤_)

where

infixr 2 _×_
infixr 4 _,_

data _⊎_ (A B : Set) : Set where
  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B

data _×_ (A B : Set) : Set where
  _,_ : A → B → A × B

data Σ (A : Set) (B : A → Set) : Set where
  _,_ : (a : A) → B a → Σ A B

-------------------------------

infixr 0  _⇒_
infixr 5  _∨_
infixr 6  _∧_

-------------------------------

TPred = Time → Set
TimePred = TPred

-------------------------------

-- Lifted Logical Operators

_∨_ : TPred → TPred → TPred
(φ ∨ ψ) t = φ t ⊎ ψ t

_∧_ : TPred → TPred → TPred
(φ ∧ ψ) t = φ t × ψ t

_⇒_ : TPred → TPred → TPred
(φ ⇒ ψ) t = φ t → ψ t

⊥ : TPred
⊥ t = ⊥₀

⊤ : TPred
⊤ t = ⊤₀

¬_ : TPred → TPred
¬ φ = φ ⇒ ⊥

-----------------------------------------

FromInitial : TPred → Set
FromInitial φ = φ initial

⟦_⟧ = FromInitial

-- Unary Temporal Operators

-- Global

□ : TPred → TPred
□ φ t = (t' : Time) → t ≤ t' → φ t'

□¬ : TPred → TPred
□¬ φ = □ (¬ φ)

-- Future

◇ : TPred → TPred
◇ φ t = Σ _ (λ t' → t ≤ t' × φ t')

◇¬ : TPred → TPred
◇¬ φ = ◇ (¬ φ)

-- Binary Temporal Operators

_[_,_⟩ : TPred → Time → Time → Set
φ [ s , u ⟩ = ∀ t → s ≤ t → t ≤ u → φ t

-- Until

_U_ : TPred → TPred → TPred
φ U ψ = λ s → Σ _ (λ u → s ≤ u × φ [ s , u ⟩ × ψ u)

-- Constrains

_▹_ : TPred → TPred → TPred
φ ▹ ψ = λ s → ∀ u → s ≤ u → φ [ s , u ⟩ → ψ u
