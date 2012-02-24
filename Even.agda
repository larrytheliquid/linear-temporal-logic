open import FRP.JS.True
open import FRP.JS.Nat

module Even where

data Even : ℕ → Set where
  zero : Even 0
  suc : ∀ {n} → Even n → Even (suc (suc n))

-- An evens-only traversal starting from any even number

data Evens : ℕ → ℕ → Set where
  zero : Evens 0 2
  suc : ∀ {m n} → Evens m n → Evens m (suc (suc n))
  start : ∀ {m n} → Evens m n → Evens n (suc (suc n))

eg : Evens 0 6
eg = suc (suc zero)

eg₂ : Evens 2 6
eg₂ = suc (start zero)

eg₃ : Evens 6 14
eg₃ = suc (suc (suc (start (suc (suc zero)))))

eg₄ : Evens 1 2 → ⊥
eg₄ (suc ())

eg₅ : Evens 6 2 → ⊥
eg₅ (suc ())

eg₆ : Evens 5 8 → ⊥
eg₆ (suc (suc (suc (suc ()))))

eg₇ : ∀ n → Evens 5 n → ⊥
eg₇ .(suc (suc n)) (suc {.5} {n} y) = eg₇ n y
eg₇ .7 (start (suc (suc ())))
eg₇ .7 (start (suc (start ())))
eg₇ .7 (start (start (suc ())))
eg₇ .7 (start (start (start ())))
