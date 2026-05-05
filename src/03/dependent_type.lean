#check Nat.add_zero  -- forall n, n + 0 = n

/-- Nat.add_zero n の型は n に依存する -/
#check Nat.add_zero 0  -- 0 + 0 = 0
#check Nat.add_zero 1  -- 1 + 0 = 1

/-- forall は実は dependent type の表現 -/
example : (forall n : Nat, n = n) = ((n : Nat) -> n = n) := by
  rfl

/-- List を MyList として再定義 -/
inductive MyList (t : Type) where
  | nil : MyList t
  | cons : t -> MyList t -> MyList t

example : MyList Nat := MyList.nil
example : MyList Nat := MyList.cons 1 MyList.nil

/-- さらに MyList に長さを追加する (依存型) -/
inductive MyVect (t : Type) : Nat -> Type where
  | nil : MyVect t 0
  | cons : (n : Nat) -> t -> MyVect t n -> MyVect t (n + 1)

example : MyVect Nat 0 := MyVect.nil
example : MyVect Nat 1 := MyVect.cons 0 1 MyVect.nil

/-- 依存ペア (a, b) で b の型が a に依存する -/
example : (a : Type) ×  a := ⟨Nat, 0⟩
example : (a : Type) ×  a := ⟨List Nat, [1, 2, 3]⟩

example : List ((a : Type) ×  a) := [⟨Nat, 0⟩, ⟨Bool, false⟩]
example : {t : Type} -> {n : Nat} -> (x : t) -> (v : MyVect t n) -> MyVect t (n + 1) :=
  fun {_} {n} x v => MyVect.cons n x v
