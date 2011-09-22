{-# OPTIONS --type-in-type #-}
module SingleChannelTheorems where

open import NeilPrelude
open import SingleChannel
import LTL
open LTL State ¬connected∧¬member Next Next-Reflexive Next-Transitive

{- Adequacy -}

Connected∨¬Connected : TPred
Connected∨¬Connected = G (Connected ∨ ¬Connected)

proof:Connected∨¬Connected : FromInitial Connected∨¬Connected
proof:Connected∨¬Connected ¬connected∧¬member _ = inr ¬connected∧¬member
proof:Connected∨¬Connected connected∧¬member _ = inl connected∧¬member
proof:Connected∨¬Connected connected∧member _ = inl connected∧member

Member∨¬Member : TPred
Member∨¬Member = G (Member ∨ ¬Member)

proof:Member∨¬Member : FromInitial Member∨¬Member
proof:Member∨¬Member ¬connected∧¬member _ = inr ¬connected∧¬member
proof:Member∨¬Member connected∧¬member _ = inr connected∧¬member
proof:Member∨¬Member connected∧member _ = inl connected∧member

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

{- Fairness -}

Connected-Fair : TPred
Connected-Fair = G (F Connected)

proof:Connected-Fair : FromInitial Connected-Fair
proof:Connected-Fair ¬connected∧¬member _ = _ , (¬connected-nickuser , connected∧¬member)
proof:Connected-Fair connected∧¬member _ = _ , (¬member-part , connected∧¬member)
proof:Connected-Fair connected∧member _ = _ , (member-join , connected∧member)

¬Connected-Fair : TPred
¬Connected-Fair = G (F ¬Connected)

proof:¬Connected-Fair : FromInitial ¬Connected-Fair
proof:¬Connected-Fair ¬connected∧¬member _ = _ , (¬connected-quit , ¬connected∧¬member)
proof:¬Connected-Fair connected∧¬member _ = _ , (¬member-quit , ¬connected∧¬member)
proof:¬Connected-Fair connected∧member _ = _ , (member-quit , ¬connected∧¬member)

Member-Fair : TPred
Member-Fair = G (F Member)

proof:Member-Fair : FromInitial Member-Fair
proof:Member-Fair ¬connected∧¬member _ =
  _ , (¬connected-nickuser ⇛ ¬member-join , connected∧member)
proof:Member-Fair connected∧¬member _ = _ , (¬member-join , connected∧member)
proof:Member-Fair connected∧member _ = _ , (member-join , connected∧member)

¬Member-Fair : TPred
¬Member-Fair = G (F ¬Member)

proof:¬Member-Fair : FromInitial ¬Member-Fair
proof:¬Member-Fair ¬connected∧¬member _ = _ , (¬connected-part , ¬connected∧¬member)
proof:¬Member-Fair connected∧¬member _ = _ , (¬member-part , connected∧¬member)
proof:¬Member-Fair connected∧member _ = _ , (member-part , connected∧¬member)

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




