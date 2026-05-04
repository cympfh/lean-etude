inductive MyNat where
  | zero
  | succ (n : MyNat)

#check MyNat.zero
#check MyNat.succ
#check MyNat.succ .zero

def MyNat.one := MyNat.succ .zero
def MyNat.two := MyNat.succ MyNat.one

def MyNat.add (m n : MyNat) : MyNat :=
  match m with
  | MyNat.zero => n
  | MyNat.succ m' => MyNat.succ (MyNat.add m' n)

#check MyNat.add MyNat.one MyNat.two
#eval MyNat.add MyNat.one MyNat.two
#reduce MyNat.add MyNat.one MyNat.two

example : MyNat.add .one .two = MyNat.add .two .one := by
  rfl

example (n : MyNat) : MyNat.add .zero n = n := by
  simp [MyNat.add]
