def P (n: Nat) := n = n

-- forall
example : forall a, P a := by
  intro x
  dsimp [P]  -- 式展開

example (P : Nat -> Prop) : (forall x, P x) -> P 0 := by
  intro h
  exact h 0

-- exists
def even (n: Nat) := exists m, n = m + m

example : even 4 := by
  exists 2

example
  (alpha : Type)
  (P Q : alpha -> Prop)
  (h : exists x : alpha, And (P x) (Q x))
  : exists x, Q x := by
  obtain ⟨y, hy⟩ := h
  exists y
  exact hy.right

-- opaque は実装を与えない新しい定数の宣言
opaque Human : Type
/-- 人間同士の関係 --/
opaque Love : Human -> Human -> Prop
@[inherit_doc] infix:50 "-loves->" => Love

-- 全ての人に愛される人が存在する
def Idol := exists idol : Human, forall h : Human, h -loves-> idol

-- 孤独な人はいない
def YouAreNotLonely := forall h, exists i, i -loves-> h

-- 博愛主義者
def Philanthropist := exists p, forall h, p -loves-> h

-- 博愛主義者がいるならあなたは孤独ではない
example : Philanthropist -> YouAreNotLonely := by
  intro h
  obtain ⟨p, hp⟩  := h
  dsimp [YouAreNotLonely]
  intro f
  exists p
  exact hp f

-- 排中律を使う
example (P : Prop) : Not (Not P) -> P := by
  intro h
  by_cases pnp : P  -- (Or P (Not P)) が導入された
  case pos =>  -- P の場合
    exact pnp
  case neg =>  -- Not P の場合
    contradiction  -- 矛盾

-- 古典論理では対偶は同値
example (P Q : Prop) : (P -> Q) <-> (Not Q -> Not P) := by
  constructor <;> intro h
  case mp =>
    intro nq
    intro p
    have : Q := by
      apply h
      exact p
    contradiction
  case mpr =>
    intro p
    by_cases qnq : Q
    case pos => exact qnq
    case neg =>
      have : Not P := by
        apply h
        exact qnq
      contradiction

