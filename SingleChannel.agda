module SingleChannel where

infixr 5  _⇛_

data Command : Set where
  nickuser join part quit : Command

data State : Set where
  ¬connected∧¬member : State
  connected∧¬member : State
  connected∧member : State

data Member : State → Set where
  connected∧member : Member connected∧member

data ¬Member : State → Set where
  ¬connected∧¬member : ¬Member ¬connected∧¬member
  connected∧¬member : ¬Member connected∧¬member

data Connected : State → Set where
  connected∧¬member : Connected connected∧¬member
  connected∧member : Connected connected∧member

data ¬Connected : State → Set where
  ¬connected∧¬member : ¬Connected ¬connected∧¬member

data Next : State → State → Set where
  _⇛_ : ∀ {a b c} →
    Next a b → Next b c → Next a c
  ¬connected-nickuser :
    Next ¬connected∧¬member connected∧¬member
  ¬connected-join :
    Next ¬connected∧¬member ¬connected∧¬member
  ¬connected-part :
    Next ¬connected∧¬member ¬connected∧¬member
  ¬connected-quit :
    Next ¬connected∧¬member ¬connected∧¬member

  ¬member-nickuser :
    Next connected∧¬member connected∧¬member
  ¬member-join :
    Next connected∧¬member connected∧member
  ¬member-part :
    Next connected∧¬member connected∧¬member
  ¬member-quit :
    Next connected∧¬member ¬connected∧¬member

  member-nickuser :
    Next connected∧member connected∧member
  member-join :
    Next connected∧member connected∧member
  member-part :
    Next connected∧member connected∧¬member
  member-quit :
    Next connected∧member ¬connected∧¬member

-- Next-Reflexive : Reflexive Next
-- Next-Reflexive {¬connected∧¬member} = ¬connected-join
-- Next-Reflexive {connected∧¬member} = ¬member-nickuser
-- Next-Reflexive {connected∧member} = member-nickuser

-- Next-Transitive : Transitive Next
-- Next-Transitive ab bc = ab ⇛ bc

