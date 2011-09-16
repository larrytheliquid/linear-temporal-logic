{-# OPTIONS --type-in-type #-}
module SingleChannel where
open import NeilPrelude
open import Logic

data Command : Set where
  nickuser join part quit : Command

data Connection : Set where
  connected ¬connected : Connection

data Channel : Set where
  member ¬member : Channel

data State : Set where
  ¬connected∧¬member : State
  connected∧¬member : State
  connected∧member : State

data Server : Set where
  server : Command → State → Server

data Next : Server → Server → Set where
  ¬connected-nickuser : ∀ {next} →
    Next (server nickuser ¬connected∧¬member) (server next connected∧¬member)
  ¬connected-join : ∀ {next} → 
    Next (server join ¬connected∧¬member) (server next ¬connected∧¬member)
  ¬connected-part : ∀ {next} →
    Next (server part ¬connected∧¬member) (server next ¬connected∧¬member)
  ¬connected-quit : ∀ {next} →
    Next (server quit ¬connected∧¬member) (server next ¬connected∧¬member)

  ¬member-nickuser : ∀ {next} →
    Next (server nickuser connected∧¬member) (server next connected∧¬member)
  ¬member-join : ∀ {next} →
    Next (server join connected∧¬member) (server next connected∧member)
  ¬member-part : ∀ {next} →
    Next (server part connected∧¬member) (server next connected∧¬member)
  ¬member-quit : ∀ {next} →
    Next (server nickuser connected∧¬member) (server next ¬connected∧¬member)

  member-nickuser : ∀ {next} →
    Next (server nickuser connected∧member) (server next connected∧member)
  member-join : ∀ {next} →
    Next (server join connected∧member) (server next connected∧member)
  member-part : ∀ {next} →
    Next (server part connected∧member) (server next connected∧¬member)
  member-quit : ∀ {next} →
    Next (server nickuser connected∧member) (server next ¬connected∧¬member)

Next-reflexive : Reflexive Next
Next-reflexive = {!!}

Next-transitive : Transitive Next
Next-transitive = {!!}
