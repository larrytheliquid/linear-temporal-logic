{-# OPTIONS --type-in-type #-}

open import NeilPrelude
open import Logic

module LTL

  (Time    : Set)
  (initial   : Time)
  (_≤_    : Rel Time)
  (reflex  : Reflexive _≤_)
  (transit : Transitive _≤_)

where

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
⊥ t = False

⊤ : TPred
⊤ t = True

¬_ : TPred → TPred
¬ φ = φ ⇒ ⊥

-----------------------------------------

FromInitial : TPred → Set
FromInitial φ = φ initial

-- Unary Temporal Operators

-- Global

G : TPred → TPred
G φ t = (t' : Time) → t ≤ t' → φ t'

G¬ : TPred → TPred
G¬ φ = G (¬ φ)

-- Future

F : TPred → TPred
F φ t = ∃ (λ t' → t ≤ t' × φ t')

F¬ : TPred → TPred
F¬ φ = F (¬ φ)
