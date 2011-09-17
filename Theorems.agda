{-# OPTIONS --type-in-type #-}
module Theorems where

open import NeilPrelude
open import SingleChannel
import LTL
open LTL State Next Next-Reflexive Next-Transitive

{- Adequacy -}

Connected∨¬Connected : TPred
Connected∨¬Connected = G (Connected ∨ ¬Connected)

proof:Connected∨¬Connected : ∀ {s} → Connected∨¬Connected s
proof:Connected∨¬Connected ¬connected∧¬member (x ⇛ x') = proof:Connected∨¬Connected ¬connected∧¬member x'
proof:Connected∨¬Connected ¬connected∧¬member t = inr ¬connected∧¬member
proof:Connected∨¬Connected connected∧¬member t = inl connected∧¬member
proof:Connected∨¬Connected connected∧member t = inl connected∧member

{- Safety -}

¬Connected⇒StateCleared : TPred
¬Connected⇒StateCleared = G¬ (¬Connected ∧ Member)

proof:¬Connected⇒StateCleared : ∀ s → ¬Connected⇒StateCleared s
proof:¬Connected⇒StateCleared ¬connected∧¬member f
  with f _ ¬connected-join
... | _ , ()
proof:¬Connected⇒StateCleared connected∧¬member f
  with f _ ¬member-part
... | _ , ()
proof:¬Connected⇒StateCleared connected∧member f
  with f _ member-join
... | () , _

