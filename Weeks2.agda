import LTL

module Weeks2 where

data Day : Set where
  mon tue wed thu fri sat sun : Day

data Next : Day → Day → Set where
  mon : Next mon tue
  tue : Next tue wed
  wed : Next wed thu
  thu : Next thu fri
  fri : Next fri sat
  sat : Next sat sun

data _≤_ : Day → Day → Set where
  next : ∀ {t u} → Next t u → t ≤ u
  trans : ∀ {s t u} → s ≤ t → t ≤ u → s ≤ u

eg₂ : mon ≤ tue
eg₂ = next mon

eg₃ : mon ≤ wed
eg₃ = trans (next mon) (next tue)

eg₄ : mon ≤ thu
eg₄ = trans (next mon) (trans (next tue) (next wed))

mon≤sat : mon ≤ sat
mon≤sat = trans (next mon) (trans (next tue) (trans (next wed) (trans (next thu) (next fri))))

data Weekday : Day → Set where
  mon : Weekday mon
  tue : Weekday tue
  wed : Weekday wed
  thu : Weekday thu
  fri : Weekday fri

data Weekend : Day → Set where
  sat : Weekend sat
  sun : Weekend sun

open LTL Day mon _≤_

□Weeday∨Weekend : ⟦ □ (Weekday ∨ Weekend) ⟧
□Weeday∨Weekend mon _ = inj₁ mon
□Weeday∨Weekend tue _ = inj₁ tue
□Weeday∨Weekend wed _ = inj₁ wed
□Weeday∨Weekend thu _ = inj₁ thu
□Weeday∨Weekend fri _ = inj₁ fri
□Weeday∨Weekend sat _ = inj₂ sat
□Weeday∨Weekend sun _ = inj₂ sun

□¬Weeday∨Weekend : ⟦ □¬ (Weekday ∧ Weekend) ⟧
□¬Weeday∨Weekend mon _ (mon , ())
□¬Weeday∨Weekend tue _ (tue , ())
□¬Weeday∨Weekend wed _ (wed , ())
□¬Weeday∨Weekend thu _ (thu , ())
□¬Weeday∨Weekend fri _ (fri , ())
□¬Weeday∨Weekend sat _ (() , sat)
□¬Weeday∨Weekend sun _ (() , sun)

WeekdayUWeekend : ⟦ Weekday U Weekend ⟧
WeekdayUWeekend = sat , f where
  postulate
    g : (t : Day) → mon ≤ t → t ≤ sat → Weekday t
    -- g a (next fri) = fri
    -- g a (trans x y) = {!!}

  f : mon ≤ sat × ((t : Day) → mon ≤ t → t ≤ sat → Weekday t) × Weekend sat
  f = mon≤sat , g , sat



