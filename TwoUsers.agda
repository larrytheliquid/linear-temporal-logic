{-# OPTIONS --type-in-type #-}
module TwoUsers where
open import NeilPrelude
open import Logic

data User : Set where
  bob sally : User

data Command : Set where
  nickuser join part quit : User → Command

data State : Set where
  bob≡disc∧sally≡disc : State

  bob≡out∧sally≡out : State
  bob≡disc∧sally≡out : State
  bob≡out∧sally≡disc : State

  bob≡in∧sally≡in : State
  bob≡in∧sally≡disc : State
  bob≡disc∧sally≡in : State
  bob≡in∧sally≡out : State
  bob≡out∧sally≡in : State

data ¬Connected : User → State → Set where
  bob≡disc∧sally≡disc⊨bob≡disc : ¬Connected bob bob≡disc∧sally≡disc
  bob≡disc∧sally≡out⊨bob≡disc : ¬Connected bob bob≡disc∧sally≡out
  bob≡disc∧sally≡in⊨bob≡disc : ¬Connected bob bob≡disc∧sally≡in

  bob≡disc∧sally≡disc⊨sally≡disc : ¬Connected sally bob≡disc∧sally≡disc
  bob≡out∧sally≡disc⊨sally≡disc : ¬Connected sally bob≡out∧sally≡disc
  bob≡in∧sally≡disc⊨sally≡disc : ¬Connected sally bob≡in∧sally≡disc

data Next : State → State → Set where
  bob≡disc∧sally≡disc⊢nickuser-bob :
    Next bob≡disc∧sally≡disc bob≡out∧sally≡disc
  bob≡disc∧sally≡disc⊢nickuser-sally :
    Next bob≡disc∧sally≡disc bob≡disc∧sally≡out
  bob≡disc∧sally≡disc⊢join-bob :
    Next bob≡disc∧sally≡disc bob≡disc∧sally≡disc
  bob≡disc∧sally≡disc⊢join-sally :
    Next bob≡disc∧sally≡disc bob≡disc∧sally≡disc
  bob≡disc∧sally≡disc⊢part-bob :
    Next bob≡disc∧sally≡disc bob≡disc∧sally≡disc
  bob≡disc∧sally≡disc⊢part-sally :
    Next bob≡disc∧sally≡disc bob≡disc∧sally≡disc
  bob≡disc∧sally≡disc⊢quit-bob :
    Next bob≡disc∧sally≡disc bob≡disc∧sally≡disc
  bob≡disc∧sally≡disc⊢quit-sally :
    Next bob≡disc∧sally≡disc bob≡disc∧sally≡disc

  ---
  ---
  ---

  bob≡out∧sally≡disc⊢nickuser-bob :
    Next bob≡out∧sally≡disc bob≡out∧sally≡disc
  bob≡out∧sally≡disc⊢join-bob :
    Next bob≡out∧sally≡disc bob≡in∧sally≡disc
  bob≡out∧sally≡disc⊢part-bob :
    Next bob≡out∧sally≡disc bob≡out∧sally≡disc
  bob≡out∧sally≡disc⊢quit-bob :
    Next bob≡out∧sally≡disc bob≡disc∧sally≡disc
  ---
  bob≡out∧sally≡out⊢nickuser-bob :
    Next bob≡out∧sally≡out bob≡out∧sally≡out
  bob≡out∧sally≡out⊢join-bob :
    Next bob≡out∧sally≡out bob≡in∧sally≡out
  bob≡out∧sally≡out⊢part-bob :
    Next bob≡out∧sally≡out bob≡out∧sally≡out
  bob≡out∧sally≡out⊢quit-bob :
    Next bob≡out∧sally≡out bob≡disc∧sally≡out
  ---
  bob≡out∧sally≡in⊢nickuser-bob :
    Next bob≡out∧sally≡in bob≡out∧sally≡in
  bob≡out∧sally≡in⊢join-bob :
    Next bob≡out∧sally≡in bob≡in∧sally≡in
  bob≡out∧sally≡in⊢part-bob :
    Next bob≡out∧sally≡in bob≡out∧sally≡in
  bob≡out∧sally≡in⊢quit-bob :
    Next bob≡out∧sally≡in bob≡disc∧sally≡in

  bob≡in∧sally≡disc⊢nickuser-bob :
    Next bob≡in∧sally≡disc bob≡in∧sally≡disc
  bob≡in∧sally≡disc⊢join-bob :
    Next bob≡in∧sally≡disc bob≡in∧sally≡disc
  bob≡in∧sally≡disc⊢part-bob :
    Next bob≡in∧sally≡disc bob≡out∧sally≡disc
  bob≡in∧sally≡disc⊢quit-bob :
    Next bob≡in∧sally≡disc bob≡disc∧sally≡disc
  ---
  bob≡in∧sally≡out⊢nickuser-bob :
    Next bob≡in∧sally≡out bob≡in∧sally≡out
  bob≡in∧sally≡out⊢join-bob :
    Next bob≡in∧sally≡out bob≡in∧sally≡out
  bob≡in∧sally≡out⊢part-bob :
    Next bob≡in∧sally≡out bob≡out∧sally≡out
  bob≡in∧sally≡out⊢quit-bob :
    Next bob≡in∧sally≡out bob≡disc∧sally≡out
  ---
  bob≡in∧sally≡in⊢nickuser-bob :
    Next bob≡in∧sally≡in bob≡in∧sally≡in
  bob≡in∧sally≡in⊢join-bob :
    Next bob≡in∧sally≡in bob≡in∧sally≡in
  bob≡in∧sally≡in⊢part-bob :
    Next bob≡in∧sally≡in bob≡out∧sally≡in
  bob≡in∧sally≡in⊢quit-bob :
    Next bob≡in∧sally≡in bob≡disc∧sally≡in

  ---
  ---
  ---

  sally≡out∧bob≡disc⊢nickuser-sally :
    Next sally≡out∧bob≡disc sally≡out∧bob≡disc
  sally≡out∧bob≡disc⊢join-sally :
    Next sally≡out∧bob≡disc sally≡in∧bob≡disc
  sally≡out∧bob≡disc⊢part-sally :
    Next sally≡out∧bob≡disc sally≡out∧bob≡disc
  sally≡out∧bob≡disc⊢quit-sally :
    Next sally≡out∧bob≡disc sally≡disc∧bob≡disc
  ---
  sally≡out∧bob≡out⊢nickuser-sally :
    Next sally≡out∧bob≡out sally≡out∧bob≡out
  sally≡out∧bob≡out⊢join-sally :
    Next sally≡out∧bob≡out sally≡in∧bob≡out
  sally≡out∧bob≡out⊢part-sally :
    Next sally≡out∧bob≡out sally≡out∧bob≡out
  sally≡out∧bob≡out⊢quit-sally :
    Next sally≡out∧bob≡out sally≡disc∧bob≡out
  ---
  sally≡out∧bob≡in⊢nickuser-sally :
    Next sally≡out∧bob≡in sally≡out∧bob≡in
  sally≡out∧bob≡in⊢join-sally :
    Next sally≡out∧bob≡in sally≡in∧bob≡in
  sally≡out∧bob≡in⊢part-sally :
    Next sally≡out∧bob≡in sally≡out∧bob≡in
  sally≡out∧bob≡in⊢quit-sally :
    Next sally≡out∧bob≡in sally≡disc∧bob≡in

  sally≡in∧bob≡disc⊢nickuser-sally :
    Next sally≡in∧bob≡disc sally≡in∧bob≡disc
  sally≡in∧bob≡disc⊢join-sally :
    Next sally≡in∧bob≡disc sally≡in∧bob≡disc
  sally≡in∧bob≡disc⊢part-sally :
    Next sally≡in∧bob≡disc sally≡out∧bob≡disc
  sally≡in∧bob≡disc⊢quit-sally :
    Next sally≡in∧bob≡disc sally≡disc∧bob≡disc
  ---
  sally≡in∧bob≡out⊢nickuser-sally :
    Next sally≡in∧bob≡out sally≡in∧bob≡out
  sally≡in∧bob≡out⊢join-sally :
    Next sally≡in∧bob≡out sally≡in∧bob≡out
  sally≡in∧bob≡out⊢part-sally :
    Next sally≡in∧bob≡out sally≡out∧bob≡out
  sally≡in∧bob≡out⊢quit-sally :
    Next sally≡in∧bob≡out sally≡disc∧bob≡out
  ---
  sally≡in∧bob≡in⊢nickuser-sally :
    Next sally≡in∧bob≡in sally≡in∧bob≡in
  sally≡in∧bob≡in⊢join-sally :
    Next sally≡in∧bob≡in sally≡in∧bob≡in
  sally≡in∧bob≡in⊢part-sally :
    Next sally≡in∧bob≡in sally≡out∧bob≡in
  sally≡in∧bob≡in⊢quit-sally :
    Next sally≡in∧bob≡in sally≡disc∧bob≡in
