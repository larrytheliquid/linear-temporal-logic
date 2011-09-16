{-# OPTIONS --type-in-type #-}
module SingleChannel where
open import NeilPrelude
open import Logic

infixr 2  _⇛_

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
  server : State → Server

data Next : Server → Server → Set where
  _⇛_ : ∀ {a b c} →
    Next a b → Next b c → Next a c
  ¬connected-nickuser :
    Next (server ¬connected∧¬member) (server connected∧¬member)
  ¬connected-join :
    Next (server ¬connected∧¬member) (server ¬connected∧¬member)
  ¬connected-part :
    Next (server ¬connected∧¬member) (server ¬connected∧¬member)
  ¬connected-quit :
    Next (server ¬connected∧¬member) (server ¬connected∧¬member)

  ¬member-nickuser :
    Next (server connected∧¬member) (server connected∧¬member)
  ¬member-join :
    Next (server connected∧¬member) (server connected∧member)
  ¬member-part :
    Next (server connected∧¬member) (server connected∧¬member)
  ¬member-quit :
    Next (server connected∧¬member) (server ¬connected∧¬member)

  member-nickuser :
    Next (server connected∧member) (server connected∧member)
  member-join :
    Next (server connected∧member) (server connected∧member)
  member-part :
    Next (server connected∧member) (server connected∧¬member)
  member-quit :
    Next (server connected∧member) (server ¬connected∧¬member)

Next-Reflexive : Reflexive Next
Next-Reflexive {server ¬connected∧¬member} = ¬connected-join
Next-Reflexive {server connected∧¬member} = ¬member-nickuser
Next-Reflexive {server connected∧member} = member-nickuser

Next-Transitive : Transitive Next
Next-Transitive ab bc = ab ⇛ bc
