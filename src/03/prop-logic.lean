#check (1 + 1 = 3 : Prop)
#check (fun n => n + 1 = 3 : Nat -> Prop)

example : True := by
  trivial

example (P : Prop) (h : P) : P := by
  exact h

-- 三段論法
example (P Q : Prop) (h1 : P -> Q) (h2 : P) : Q := by
  apply h1
  exact h2

#check Not True
#check Not False

-- not は False への implication として定義される
example (P : Prop) : (Not P) = (P -> False) := by
  trivial

-- P と Not P は同時に成り立たない
example (P : Prop) (hp : P) (hnp : Not P) : False := by
  apply hnp
  exact hp

-- 対偶
example (P Q : Prop) : (P -> Not Q) -> (Q -> Not P) := by
  intro h
  intro q
  intro p
  apply h
  exact p
  exact q

-- 爆発律
example (P : Prop) : (p : P) -> (notp : Not P) -> False := by
  intro p np
  contradiction  -- 前提に矛盾があるので、どんな結論も導ける

example (P Q : Prop) (notp : Not P) (p : P) : Q := by
  exfalso  -- Goal を False に変更する
  contradiction

-- 同値性
example (P Q : Prop) (h1 : P -> Q) (h2 : Q -> P) : P <-> Q := by
  constructor
  · exact h1
  · exact h2

example (P Q : Prop) (q : Q) : (Q -> P) <-> P := by
  constructor
  case mp =>
    intro qp
    apply qp
    exact q
  case mpr =>
    intro p q2
    trivial



