#check Classical.em  -- Exclude Middle (EM) : P or not P
#check Classical.choice

/-- 全射性 -/
def Surjective {X Y : Type} (f : X -> Y) : Prop :=
  forall y : Y, exists x : X, f x = y

/-- 恒等写像は全射 -/
example : Surjective (fun n : Nat => n) := by
  intro y
  exists y

/-- 全射 f は右逆写像 g を持つ
ただし構成方法は与えられない (noncomputable) -/
noncomputable def rightInverse (f : X -> Y) (fh : Surjective f) : Y -> X := by
  intro y
  have : Nonempty {x // f x = y} := by
    let ⟨x, hx⟩ := fh y
    exact ⟨⟨x, hx⟩⟩
  have x := Classical.choice this
  exact x.val


/-- 対偶が同値であれば二重否定除去が可能になる -/
theorem double_neg_of_contra_eq (P : Prop)
  (contra_eq : forall (P Q : Prop), (P -> Q) <-> (Not Q -> Not P))
  : Not (Not P) -> P := by
    have c : (True -> P) <-> (Not P -> False) := by
      rw [contra_eq]
      simp
    have d : P <-> Not (Not P) := by
      simp
    exact d.mpr

