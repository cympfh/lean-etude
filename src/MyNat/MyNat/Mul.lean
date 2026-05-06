import MyNat.Definition
import MyNat.Add

/-- 乗算の定義 -/
def MyNat.mul (m n : MyNat) : MyNat :=
  match n with
  | 0 => 0
  | n + 1 => .mul m n + m

/-- 演算子の定義 -/
instance : Mul MyNat where
  mul := MyNat.mul

@[simp]
theorem MyNat.mul_zero (m : MyNat) : m * 0 = 0 := rfl

@[simp]
theorem MyNat.zero_mul (m : MyNat) : 0 * m = 0 := by
  induction m with
  | zero => simp
  | succ m' ih =>
    calc
      _ = (0 * m') + 0 := by rfl
      _ = 0 + 0 := by rw [ih]

@[simp]
theorem MyNat.right_one_is_id (m : MyNat) : m * 1 = m := by
  calc
    _ = (m * 0) + m := by rfl
    _ = m := by simp

@[simp]
theorem MyNat.left_one_is_id (m : MyNat) : 1 * m = m := by
  induction m with
  | zero => simp
  | succ m' ih =>
    calc
      _ = (1 * m') + 1 := by rfl
      _ = m' + 1 := by rw [ih]

@[simp]
theorem MyNat.add_one_mul (m n : MyNat) : (m + 1) * n = (m * n) + n := by
  induction n with
  | zero => simp
  | succ n' ih =>
    calc
      _ = ((m + 1) * n') + (m + 1) := by rfl
      _ = ((m * n') + n') + (m + 1) := by rw [ih]
      _ = (m * n' + m + n' + 1) := by ac_rfl

/-- 交換法則 -/
theorem MyNat.mul_comm (m n : MyNat) : m * n = n * m := by
  induction n with
  | zero => simp
  | succ n' ih =>
     calc
       _ = (m * n') + m := by rfl
       _ = (n' * m) + m := by rw [ih]
       _ = (n' + 1) * m := by rw [add_one_mul]

-- ac_rfl に登録
instance : Std.Commutative (α := MyNat) (· * ·) where
  comm := MyNat.mul_comm

/-- 左分配法則 -/
@[simp]
theorem MyNat.mul_add (m n k : MyNat) : m * (n + k) = m * n + m * k := by
  induction k with
  | zero => simp
  | succ k' ih =>
    calc
      _ = m * (n + k').succ := by rfl
      _ = m * (n + k') + m := by rfl
      _ = (m * n + m * k') + m := by rw [ih]
      _ = m * n + (m * k' + m) := by ac_rfl
      _ = m * n + m * k'.succ := by rfl

/-- 右分配法則 -/
@[simp]
theorem MyNat.add_mul (m n k : MyNat) : (m + n) * k = m * k + n * k := by
  induction k with
  | zero => simp
  | succ k' ih =>
    calc
      _ = (m + n) * k' + (m + n) := by rfl
      _ = (m * k' + n * k') + (m + n) := by rw [ih]
      _ = (m * k' + m) + (n * k' + n) := by ac_rfl
      _ = m * k'.succ + n * k'.succ := by rfl

/-- 結合法則 -/
theorem MyNat.mul_assoc (m n k : MyNat) : (m * n) * k = m * (n * k) := by
  induction k with
  | zero => simp
  | succ k' ih =>
    calc
      _ = (m * n * k') + (m * n) := by rfl
      _ = (m * (n * k')) + (m * n) := by rw [ih]
      _ = m * (n * k' + n) := by simp

instance : Std.Associative (α := MyNat) (· * ·) where
  assoc := MyNat.mul_assoc

example : (m + n) * (m + n) = m * m + 2 * m * n + n * n := by
  have (x : MyNat) : x + x = 2 * x := by
    calc
      _ = 1 * x + 1 * x := by simp
      _ = (1 + 1) * x := by simp
      _ = 2 * x := by rfl
  calc
    _ = m * (m + n) + n * (m + n) := by rw [MyNat.add_mul]
    _ = (m * m + m * n) + n * (m + n) := by rw [MyNat.mul_add]
    _ = (m * m + m * n) + (n * m + n * n) := by rw [MyNat.mul_add]
    _ = m * m + (m * n + m * n) + n * n := by ac_rfl
    _ = m * m + 2 * (m * n) + n * n := by rw [this (m * n)]
    _ = m * m + 2 * m * n + n * n := by ac_rfl

/-- 分配法則を適用する tactics の定義 -/
macro "distrib" : tactic => `(tactic| simp only [MyNat.mul_add, MyNat.add_mul])

example (a b c d : MyNat) : (a + b) * (c + d) = a * c + a * d + b * c + b * d := by
  distrib
  ac_rfl

-- focus タクティクスは複数のタクティクの逐次適用する
-- try タクティクは失敗してもエラーを出さない
macro "distrib" : tactic => `(tactic| focus
  try rw [show 3 = 1 + 2 by rfl]
  try rw [show 2 = 1 + 1 by rfl]
  try simp only [MyNat.zero_mul, MyNat.mul_zero, MyNat.right_one_is_id, MyNat.left_one_is_id]
  try simp only [MyNat.mul_add, MyNat.add_mul]
  try ac_rfl
)

example : (m + n) * m + n * 2 * m = m * m + 3 * m * n := by
  distrib
  distrib

example (n : MyNat) : exists s t : MyNat, s * t = n * n + 8 * n + 16 := by
  exists (n + 4), (n + 4)
  distrib
  calc
    _ = n * n + 4 * n + 4 * n + 4 * 4 := by ac_rfl
    _ = n * n + (4 + 4) * n + 4 * 4 := by distrib
