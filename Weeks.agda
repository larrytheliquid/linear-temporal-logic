import LTL

module Weeks where

infixr 5  _⇛_

data Day : Set where
  mon tue wed thu fri sat sun : Day

data Later : Day → Day → Set where
  _⇛_ : ∀ {a b c} →
    Later a b → Later b c → Later a c
  mon : Later mon tue
  tue : Later tue wed
  wed : Later wed thu
  thu : Later thu fri
  fri : Later fri sat
  sat : Later sat sun
  sun : Later sun mon

data Weekday : Day → Set where
  mon : Weekday mon
  tue : Weekday tue
  wed : Weekday wed
  thu : Weekday thu
  fri : Weekday fri

data Weekend : Day → Set where
  sat : Weekend sat
  sun : Weekend sun

open LTL Day mon Later

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
  g : ∀ {t} → Later mon t → Later t sat → Weekday t
  -- g mon b = tue
  -- g {t} (x ⇛ y) b = {!!}
  g {mon} a b = mon
  g {tue} a b = tue
  g {wed} a b = wed
  g {thu} a b = thu
  g {fri} a b = fri
  g {sat} a (y ⇛ y') = {!!}
  g {sun} a b = {!!}

  f : Later mon sat × (∀ {t} → Later mon t → Later t sat → Weekday t) × Weekend sat
  f = mon ⇛ tue ⇛ wed ⇛ thu ⇛ fri , {!!} , sat
