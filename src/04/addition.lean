inductive MyNat where
  | zero : MyNat
  | succ : MyNat → MyNat

def MyNat.add (m n : MyNat) : MyNat :=
  match n with
  | MyNat.zero => m
  | MyNat.succ n' => MyNat.succ (add m n')

/-- 標準 Nat から MyNat への変換関数 -/
def MyNat.ofNat (n : Nat) : MyNat :=
  match n with
  | 0 => MyNat.zero
  | Nat.succ n' => MyNat.succ (MyNat.ofNat n')

/-- 数値リテラルを MyNat として解釈するためのインスタンス -/
@[default_instance]
instance (n : Nat) : OfNat MyNat n where
  ofNat := MyNat.ofNat n

#check 42 -- MyNat

/-- 演算子 + の定義 -/
instance : Add MyNat where
  add := MyNat.add

#eval 2 + 3

/-- MyNat -> Nat -/
def MyNat.toNat (n : MyNat) : Nat :=
  match n with
  | MyNat.zero => 0
  | MyNat.succ n' => Nat.succ (toNat n')

/-- Repr (print) -/
instance : Repr MyNat where
  reprPrec n _ := toString (MyNat.toNat n)

#eval repr (2 + 3) -- "5"

/-- 単純な add の性質の証明 -/
theorem MyNat.add_zero : n + 0 = n := by
  rfl

theorem MyNat.zero_add : 0 + n = n := by
  induction n with
  | zero => rfl
  | succ n' ih =>
    rw [show 0 + MyNat.succ n' = MyNat.succ (0 + n') from rfl]
    rw [ih]

example : 1 + n = n.succ := by
  induction n with
  | zero =>
    rw [show 1 + MyNat.zero = MyNat.zero.succ from rfl]
  | succ n' ih =>
    have : 1 + n'.succ = n'.succ.succ := by
      rw [show 1 + MyNat.succ n' = MyNat.succ (1 + n') from rfl]
      rw [ih]
    exact this

-- simp は単純な等式変形による証明を自動化する

-- simp で使う証明済み等式を登録する
attribute [simp] MyNat.add_zero MyNat.zero_add

example : 0 + (n + 0) = n := by
  simp

example : (0 + n) + 1 = n + 1 := by
  simp

example (m n : MyNat) (h : m + 0 = n) : (m + 0) + 0 = n := by
  simp_all  -- ゴールも前提も全て simp する

/-- @[simp] タグは証明したら自動で simp に登録される -/
@[simp]
theorem MyNat.zero_is_zero : MyNat.zero = 0 := rfl

/-- calc は具体的に等式を示してこれによる書き換えを行う -/
@[simp]
theorem MyNat.succ_add (m n : MyNat) : m.succ + n = (m + n).succ := by
  induction n with
  | zero => simp
  | succ n' ih =>
    calc
      _ = (m.succ + n').succ := by rfl  -- 左辺の `_` はゴールの左辺
      _ = (m + n').succ.succ := by rw [ih]  -- 左辺の `_` は前の行の右辺

@[simp]
theorem MyNat.add_one : n + 1 = 1 + n := by
  induction n with
  | zero => simp
  | succ n' ih =>
    calc
      _ = n'.succ.succ := by rfl
      _ = (n' + 1).succ := by rfl
      _ = (1 + n').succ := by rw [ih]

theorem MyNat.add_two : n + 2 = 2 + n := by
  induction n with
  | zero => simp
  | succ n' ih =>
    calc
      _ = n'.succ.succ.succ := by rfl
      _ = (n' + 2).succ := by rfl
      _ = (2 + n').succ := by rw [ih]

/-- 交換法則 -/
theorem MyNat.add_comm (m n : MyNat) : m + n = n + m := by
  induction n with
  | zero => simp
  | succ n' ih =>
    calc
      _ = (m + n').succ := by rfl
      _ = (n' + m).succ := by rw [ih]
      _ = (n'.succ + m) := by simp

/-- 結合法則 -/
theorem MyNat.add_assoc (l m n : MyNat) : (l + m) + n = l + (m + n) := by
  induction n with
  | zero => simp
  | succ n' ih =>
    calc
      _ = ((l + m) + n').succ := by rfl
      _ = (l + (m + n')).succ := by rw [ih]

/-- 結合法則と交換法則は式の単純化ではないので (?) simp では自動で使われない -/
example : l + m + n + 3 = 3 + (n + m) + l := by
  -- simp failed
  sorry

instance : Std.Associative (α := MyNat) (· + ·) where
  assoc := MyNat.add_assoc

instance : Std.Commutative (α := MyNat) (· + ·) where
  comm := MyNat.add_comm

example : l + m + n + 3 = 3 + (n + m) + l := by
  ac_rfl  -- Assoc/Comm を使って rfl する


/-- -1 函数 -/
def MyNat.pred (n : MyNat) : MyNat :=
  match n with
  | zero => zero
  | succ n' => n'

example (n : MyNat) : (n.pred + 1).pred = n.pred := by
  induction n with
  | zero =>
    simp
    rw [show .pred 0 = 0 from rfl]
    simp
    rw [show .pred 1 = 0 from rfl]
  | succ n' ih =>
    rw [show n'.succ.pred = n' from rfl]
    rw [show (n' + 1).pred = n' from rfl]
