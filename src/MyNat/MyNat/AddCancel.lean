import MyNat.Definition
import MyNat.Add
import MyNat.Mul

/-- m + 1 = n + 1 -> m = n
injection は帰納的構成が単射であることを利用して、等式から構成要素の等式を導く -/
example (h : m + 1 = n + 1) : m = n := by
  injection h

variable {l m n : MyNat}

/-- (+m) も単射なので戻せる -/
@[simp] theorem add_right_cancel (h : l + m = n + m) : l = n := by
  induction m with
  | zero => simp_all
  | succ m' ih =>
    have : l + m' = n + m' := by
      injection h
    apply ih this

/-- (m+) も単射なので戻せる -/
@[simp] theorem add_left_cancel (h : m + l = m + n) : l = n := by
  have : l + m = n + m := by
    calc
      _ = m + l := by ac_rfl
      _ = m + n := by rw [h]
      _ = n + m := by ac_rfl
  apply add_right_cancel this

example (h : m + 2 = n + 2) : m = n := by
  try simp_all -- simp に add_right_cancel が無視される...
  sorry

/-- なんか iff だと simp が使ってくれれ -/
@[simp] theorem add_right_cancel_iff : (l + m = n + m) ↔ (l = n) := by
  constructor
  · apply add_right_cancel
  · intro h
    rw [h]

example (h : m + 2 = n + 2) : m = n := by
  simp_all

@[simp] theorem add_left_cancel_iff : (m + l = m + n) ↔ (l = n) := by
  constructor
  · apply add_left_cancel
  · intro h
    rw [h]

/-- m + n = m -> n = 0 -/
@[simp] theorem add_right_eq_self : m + n = m -> n = 0 := by
  intro h
  rw [show m + n = m <-> m + n = m + 0 from by simp] at h
  simp only [add_left_cancel_iff] at h
  exact h

theorem sum_zero : m + n = 0 -> m = 0 /\ n = 0 := by
  intro h
  induction n with
  | zero =>
    simp_all
  | succ n' ih =>
    exfalso
    rw [show m + n'.succ = (m + n') + 1 from by rfl] at h
    injection h

@[simp]
theorem MyNat.sum_zero_iff : m + n = 0 <-> m = 0 /\ n = 0 := by
  constructor
  · apply sum_zero
  · rintro ⟨rfl, rfl⟩
    simp

@[simp]
theorem MyNat.mul_zero_iff : m * n = 0 <-> m = 0 ∨ n = 0 := by
  constructor
  case mp =>
    intro h
    induction n
    case zero => right; rfl
    case succ n' ih =>
      left
      rw [show m * n'.succ = (m * n') + m from by rfl] at h
      simp_all
  case mpr =>
    rintro (h | h) <;> simp_all

example : n + (1 + m) = n + 2 -> m = 1 := by
  rw [show 2 = 1 + 1 from rfl]
  simp_all



