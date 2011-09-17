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

{- Reachability -}

Connected-Reachable : TPred
Connected-Reachable = F Connected

proof:Connected-Reachable : ∀ s → Connected-Reachable s
proof:Connected-Reachable ¬connected∧¬member = _ , (¬connected-nickuser , connected∧¬member)
proof:Connected-Reachable connected∧¬member = _ , (¬member-part , connected∧¬member)
proof:Connected-Reachable connected∧member = _ , (member-join , connected∧member)

¬Connected-Reachable : TPred
¬Connected-Reachable = F ¬Connected

proof:¬Connected-Reachable : ∀ s → ¬Connected-Reachable s
proof:¬Connected-Reachable ¬connected∧¬member = _ , (¬connected-quit , ¬connected∧¬member)
proof:¬Connected-Reachable connected∧¬member = _ , (¬member-quit , ¬connected∧¬member)
proof:¬Connected-Reachable connected∧member = _ , (member-quit , ¬connected∧¬member)

Member-Reachable : TPred
Member-Reachable = F Member

proof:Member-Reachable : ∀ s → Member-Reachable s
proof:Member-Reachable ¬connected∧¬member =
  _ , (¬connected-nickuser ⇛ ¬member-join , connected∧member)
proof:Member-Reachable connected∧¬member = _ , (¬member-join , connected∧member)
proof:Member-Reachable connected∧member = _ , (member-join , connected∧member)

¬Member-Reachable : TPred
¬Member-Reachable = F ¬Member

proof:¬Member-Reachable : ∀ s → ¬Member-Reachable s
proof:¬Member-Reachable ¬connected∧¬member =
  _ , (¬connected-part , ¬connected∧¬member)
proof:¬Member-Reachable connected∧¬member = _ , (¬member-part , connected∧¬member)
proof:¬Member-Reachable connected∧member = _ , (member-part , connected∧¬member)

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


