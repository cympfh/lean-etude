def identity : Nat -> Nat := by?
  intro x
  exact x

#eval identity 5

example (P Q : Prop) (hp : P) : Q -> P :=
  fun _ => hp
