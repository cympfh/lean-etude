-- ローカル補題を作る have
example (P : Prop) : ¬ ¬ ¬ P -> ¬ P := by
  intro hn3p
  intro hp

  -- ここで Not Not P である. なぜなら
  have : ¬ ¬ P := by
    intro hnp
    contradiction
  -- 補題は this の名前で前提に入る

  contradiction

-- ゴールを変更する suffices
example (P : Prop) : ¬ ¬ (P ∨ ¬ P) := by
  intro h
  
  -- ここで Not P を示せさえすれば十分である. なぜなら
  suffices hyp : ¬ P from by
   apply h
   right
   exact hyp
  -- ゴールが ¬ P に変わる

  intro hp
  apply h
  left
  exact hp

-- 自動で定理を探してきて適用してくれる exact?
example (P : Prop) : (P -> True) <-> True := by
  exact?

-- 実は変数宣言はしなくても自動で推論してくれる
example : (True -> P) <-> P := by
  exact?

example : P <-> P := by
  exact?

-- もっと簡易的な補題は show ... from by ...
example (h : ¬ P <-> Q) : (P -> False) <-> Q := by
  rewrite [show (P -> False) <-> ¬ P from by trivial]
  exact h

-- 練習問題
example : ¬ (P <-> ¬ P) := by
  intro h
  obtain ⟨h1, h2⟩ := h
  have p : P := by
    apply h2
    intro p
    have np : ¬ P := by
      apply h1
      exact p
    contradiction
  have notp : ¬ P := by
    apply h1
    exact p
  contradiction
