{-# OPTIONS --type-in-type #-}
module Theorems where

open import NeilPrelude
open import SingleChannel
import LTL
open LTL State ¬connected∧¬member Next Next-Reflexive Next-Transitive

{- Adequacy -}

Connected∨¬Connected : TPred
Connected∨¬Connected = G (Connected ∨ ¬Connected)

proof:Connected∨¬Connected : FromInitial Connected∨¬Connected
proof:Connected∨¬Connected ¬connected∧¬member (x ⇛ x') = inr ¬connected∧¬member
proof:Connected∨¬Connected ¬connected∧¬member t = inr ¬connected∧¬member
proof:Connected∨¬Connected connected∧¬member t = inl connected∧¬member
proof:Connected∨¬Connected connected∧member t = inl connected∧member

{- Reachability -}

Connected-Reachable : TPred
Connected-Reachable = F Connected

proof:Connected-Reachable : FromInitial Connected-Reachable
proof:Connected-Reachable = _ , (¬connected-nickuser , connected∧¬member)

¬Connected-Reachable : TPred
¬Connected-Reachable = F ¬Connected

proof:¬Connected-Reachable : FromInitial ¬Connected-Reachable
proof:¬Connected-Reachable = _ , (¬connected-quit , ¬connected∧¬member)

Member-Reachable : TPred
Member-Reachable = F Member

proof:Member-Reachable : FromInitial Member-Reachable
proof:Member-Reachable =
  _ , (¬connected-nickuser ⇛ ¬member-join , connected∧member)

¬Member-Reachable : TPred
¬Member-Reachable = F ¬Member

proof:¬Member-Reachable : FromInitial ¬Member-Reachable
proof:¬Member-Reachable = _ , (¬connected-part , ¬connected∧¬member)

{- Safety -}

¬Connected⇒StateCleared : TPred
¬Connected⇒StateCleared = G¬ (¬Connected ∧ Member)

proof:¬Connected⇒StateCleared : FromInitial ¬Connected⇒StateCleared
proof:¬Connected⇒StateCleared ¬connected∧¬member (x ⇛ y) (_ , ())
proof:¬Connected⇒StateCleared connected∧¬member (x ⇛ y) (() , ())
proof:¬Connected⇒StateCleared connected∧member (x ⇛ y) (() , _)
proof:¬Connected⇒StateCleared ._ ¬connected-nickuser (() , ())
proof:¬Connected⇒StateCleared ._ ¬connected-join (_ , ())
proof:¬Connected⇒StateCleared ._ ¬connected-part (_ , ())
proof:¬Connected⇒StateCleared ._ ¬connected-quit (_ , ())




