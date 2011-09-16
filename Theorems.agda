{-# OPTIONS --type-in-type #-}
module Theorems where

open import NeilPrelude
open import SingleChannel
import LTL
open LTL State Next Next-Reflexive Next-Transitive

{- Safety -}

¬Connected⇒stateless : TPred
¬Connected⇒stateless = G¬ (¬Connected ∧ Member)
