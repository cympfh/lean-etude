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
  constructor <;> intro h
  case mp =>
    apply h
    exact q
  case mpr =>
    intro q2
    apply h

-- 仮定の同値性を使う rewrite (rw)
example (P Q : Prop) (h : P <-> Q) (hp : P) : Q := by
  rewrite [h] at hp
  exact hp

example (P Q : Prop) (h : P <-> Q) (hp : P) : Q := by
  rewrite [<- h]
  exact hp

#eval And True True
#eval Or True False

-- 論理積は分解できる
example (P Q : Prop) (p : P) (q : Q) : And P Q := by
  constructor
  case left => exact p
  case right => exact q

-- .left, .right でアクセスできる
example (P Q : Prop) (h : And P Q) : P := by
  exact h.left

-- ゴールの論理和は一方を証明すればよい
example (P Q : Prop) (p : P) : Or P Q := by
  left
  exact p

-- 仮定の論理和は cases で分解できる
example (P Q : Prop) (h : Or P Q) : Or Q P := by
  cases h with
  | inl p =>
    right
    exact p
  | inr q =>
    left
    exact q

-- 練習問題
example (P Q : Prop) : (Or (Not P) Q) -> (P -> Q) := by
  intro h
  intro p
  cases h with
  | inl np =>
    exfalso
    contradiction
  | inr q =>
    exact q

-- ド・モルガン
example (P Q : Prop) : Not (Or P Q) <-> (And (Not P) (Not Q)) := by
  constructor <;> intro h
  case mp =>
    constructor
    case left =>
      intro p
      apply h
      left
      exact p
    case right =>
      intro q
      apply h
      right
      exact q
  case mpr =>
    intro h2
    cases h2 with
    | inl p =>
      apply h.left
      exact p
    | inr q =>
      apply h.right
      exact q
