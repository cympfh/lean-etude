import MyNat.Definition

/-- 加算の定義 -/
def MyNat.add (m n : MyNat) : MyNat :=
  match n with
  | MyNat.zero => m
  | MyNat.succ n' => MyNat.succ (add m n')

/-- 演算子 + の定義 -/
instance : Add MyNat where
  add := MyNat.add

/-- 基本性質 -/
@[simp]
theorem MyNat.zero_is_zero : MyNat.zero = 0 := rfl

@[simp]
theorem MyNat.add_zero : n + 0 = n := by
  calc
    _ = MyNat.add n MyNat.zero := by rfl

@[simp]
theorem MyNat.zero_add : 0 + n = n := by
  induction n with
  | zero => simp
  | succ n' ih =>
    calc
      _ = (0 + n').succ := by rfl
      _ = n'.succ := by rw [ih]

@[simp]
theorem MyNat.succ_add (m n : MyNat) : m.succ + n = (m + n).succ := by
  induction n with
  | zero => simp
  | succ n' ih =>
    calc
      _ = (m.succ + n').succ := by rfl
      _ = (m + n').succ.succ := by rw [ih]

/-- 交換法則 -/
theorem MyNat.add_comm (m n : MyNat) : m + n = n + m := by
  induction n with
  | zero => simp
  | succ n' ih =>
    calc
      _ = (m + n').succ := by rfl
      _ = (n' + m).succ := by rw [ih]
      _ = (n'.succ + m) := by simp

-- ac_rfl に登録
instance : Std.Commutative (α := MyNat) (· + ·) where
  comm := MyNat.add_comm

/-- 結合法則 -/
theorem MyNat.add_assoc (l m n : MyNat) : (l + m) + n = l + (m + n) := by
  induction n with
  | zero => simp
  | succ n' ih =>
    calc
      _ = (l + m  + n').succ := by rfl
      _ = (l + (m + n')).succ := by rw [ih]

-- ac_rfl に登録
instance : Std.Associative (α := MyNat) (· + ·) where
  assoc := MyNat.add_assoc

example : (1 + 2) + 3 = 3 + (2 + 1) := by
  ac_rfl
