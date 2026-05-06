inductive MyNat where
  | zero
  | succ (n : MyNat)

/-- 標準 Nat から MyNat への変換関数 -/
def MyNat.ofNat (n : Nat) : MyNat :=
  match n with
  | 0 => MyNat.zero
  | Nat.succ n' => MyNat.succ (MyNat.ofNat n')

/-- 数値リテラルを MyNat として解釈するためのインスタンス -/
@[default_instance]
instance (n : Nat) : OfNat MyNat n where
  ofNat := MyNat.ofNat n

/-- MyNat -> Nat -/
def MyNat.toNat (n : MyNat) : Nat :=
  match n with
  | MyNat.zero => 0
  | MyNat.succ n' => Nat.succ (toNat n')

/-- Repr (print) -/
instance : Repr MyNat where
  reprPrec n _ := toString (MyNat.toNat n)

