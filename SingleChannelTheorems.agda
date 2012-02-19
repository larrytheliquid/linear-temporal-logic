module SingleChannelTheorems where

open import SingleChannel
import LTL
open LTL State ¬connected∧¬member Next -- Next-Reflexive Next-Transitive

{- Adequacy -}

Connected∨¬Connected : TPred
Connected∨¬Connected = □ (Connected ∨ ¬Connected)

proof:Connected∨¬Connected : FromInitial Connected∨¬Connected
proof:Connected∨¬Connected ¬connected∧¬member _ = inj₂ ¬connected∧¬member
proof:Connected∨¬Connected connected∧¬member _ = inj₁ connected∧¬member
proof:Connected∨¬Connected connected∧member _ = inj₁ connected∧member

Member∨¬Member : TPred
Member∨¬Member = □ (Member ∨ ¬Member)

proof:Member∨¬Member : FromInitial Member∨¬Member
proof:Member∨¬Member ¬connected∧¬member _ = inj₂ ¬connected∧¬member
proof:Member∨¬Member connected∧¬member _ = inj₂ connected∧¬member
proof:Member∨¬Member connected∧member _ = inj₁ connected∧member

{- Reachability -}

Connected-Reachable : TPred
Connected-Reachable = ◇ Connected

proof:Connected-Reachable : FromInitial Connected-Reachable
proof:Connected-Reachable = _ , (¬connected-nickuser , connected∧¬member)

¬Connected-Reachable : TPred
¬Connected-Reachable = ◇ ¬Connected

proof:¬Connected-Reachable : FromInitial ¬Connected-Reachable
proof:¬Connected-Reachable = _ , (¬connected-quit , ¬connected∧¬member)

Member-Reachable : TPred
Member-Reachable = ◇ Member

proof:Member-Reachable : FromInitial Member-Reachable
proof:Member-Reachable =
  _ , (¬connected-nickuser ⇛ ¬member-join , connected∧member)

¬Member-Reachable : TPred
¬Member-Reachable = ◇ ¬Member

proof:¬Member-Reachable : FromInitial ¬Member-Reachable
proof:¬Member-Reachable = _ , (¬connected-part , ¬connected∧¬member)

{- Fairness -}

Connected-Fair : TPred
Connected-Fair = □ (◇ Connected)

proof:Connected-Fair : FromInitial Connected-Fair
proof:Connected-Fair ¬connected∧¬member _ = _ , (¬connected-nickuser , connected∧¬member)
proof:Connected-Fair connected∧¬member _ = _ , (¬member-part , connected∧¬member)
proof:Connected-Fair connected∧member _ = _ , (member-join , connected∧member)

¬Connected-Fair : TPred
¬Connected-Fair = □ (◇ ¬Connected)

proof:¬Connected-Fair : FromInitial ¬Connected-Fair
proof:¬Connected-Fair ¬connected∧¬member _ = _ , (¬connected-quit , ¬connected∧¬member)
proof:¬Connected-Fair connected∧¬member _ = _ , (¬member-quit , ¬connected∧¬member)
proof:¬Connected-Fair connected∧member _ = _ , (member-quit , ¬connected∧¬member)

Member-Fair : TPred
Member-Fair = □ (◇ Member)

proof:Member-Fair : FromInitial Member-Fair
proof:Member-Fair ¬connected∧¬member _ =
  _ , (¬connected-nickuser ⇛ ¬member-join , connected∧member)
proof:Member-Fair connected∧¬member _ = _ , (¬member-join , connected∧member)
proof:Member-Fair connected∧member _ = _ , (member-join , connected∧member)

¬Member-Fair : TPred
¬Member-Fair = □ (◇ ¬Member)

proof:¬Member-Fair : FromInitial ¬Member-Fair
proof:¬Member-Fair ¬connected∧¬member _ = _ , (¬connected-part , ¬connected∧¬member)
proof:¬Member-Fair connected∧¬member _ = _ , (¬member-part , connected∧¬member)
proof:¬Member-Fair connected∧member _ = _ , (member-part , connected∧¬member)

{- Safety -}

¬Connected⇒StateCleared : TPred
¬Connected⇒StateCleared = □¬ (¬Connected ∧ Member)

proof:¬Connected⇒StateCleared : FromInitial ¬Connected⇒StateCleared
proof:¬Connected⇒StateCleared ¬connected∧¬member (x ⇛ y) (_ , ())
proof:¬Connected⇒StateCleared connected∧¬member (x ⇛ y) (() , ())
proof:¬Connected⇒StateCleared connected∧member (x ⇛ y) (() , _)
proof:¬Connected⇒StateCleared ._ ¬connected-nickuser (() , ())
proof:¬Connected⇒StateCleared ._ ¬connected-join (_ , ())
proof:¬Connected⇒StateCleared ._ ¬connected-part (_ , ())
proof:¬Connected⇒StateCleared ._ ¬connected-quit (_ , ())




