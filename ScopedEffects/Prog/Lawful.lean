import ScopedEffects.Prog

namespace ScopedEffects

variable {α β : Type _} {f : α → β} {n : Nat} {es : List Effect}

namespace Prog'

theorem foldP_1 {n x} : foldP (Prog' es α) n .varZ .varS .op .scope x = x := by
  match n, x with
  | 0, .varZ x => rfl
  | n+1, .varS x =>
    show varS _ = x.varS
    rw [foldP_1]
  | n+1, .op _ _ =>
    show op _ _ = op _ _
    simp only [foldP_1]
  | n+1, .scope _ _ =>
    show scope _ _ = scope _ _
    simp only [foldP_1]

theorem pure_def {x : α} : pure (es := es) x = varS (varZ x) := by
  rfl

theorem pure_unwrap0 {x : Prog' es α 0} : pure (es := es) x.unwrap0 = varS x := by
  cases x
  rfl

theorem map_zero {x : Prog' es α 0} : map 0 f x = varZ (f x.unwrap0) := by
  cases x
  rfl

theorem map_varS {x : Prog' es α n} : map n.succ f x.varS = varS (map n f x) := by
  rfl

theorem map_op {req res} : map (es := es) n.succ f (op req res) = op req λ i ↦ map n.succ f (res i) := by
  rfl

theorem map_scope {req res} : map (es := es) n.succ f (scope req res) = scope req λ i ↦ map n.succ.succ f (res i) := by
  rfl

theorem map_id (x : Prog es α) : map 1 id x = x := by
  apply foldP_1

theorem unwrap0_varZ (x : α) : (varZ (es := es) x).unwrap0 = x :=
  rfl

theorem bind_zero_varS (x : Prog' es α 0) (f : α → Prog es β) : bind 0 x.varS f = f x.unwrap0 :=
  match x with
  | .varZ _ => rfl

theorem bind_succ_varS (x : Prog' es α (n + 1)) (f : α → Prog es β) : bind (n+1) x.varS f = (bind n x f).varS :=
  rfl

theorem bind_op (req res) (f : α → Prog es β) : bind n (op req res) f = op req λ i ↦ bind n (res i) f := by
  rfl

theorem bind_scope (req res) (f : α → Prog es β) : bind n (scope req res) f = scope req λ i ↦ bind (n + 1) (res i) f := by
  rfl

theorem bind_assoc {γ} (x : Prog es α) (f : α → Prog es β) (g : β → Prog es γ) : bind _ (bind _ x f) g = bind _ x (λ x ↦ bind _ (f x) g) :=
  let P : ∀ n, Prog' es α n → Prop := λ
    | 0, x => x = x
    | n+1, x => bind _ (bind _ x f) g = bind _ x (λ x ↦ bind _ (f x) g)
  Prog'.rec (motive := P)
    (λ _ ↦ rfl)
    (λ {n} x h ↦ match n with
    | 0 => by simp only [P, bind_zero_varS]
    | n+1 => by simp only [P, bind_succ_varS, h])
    (by
      intro n req res h
      simp only [P, bind_op, h])
    (by
      intro n req res h
      simp only [P, bind_scope, h])
    x

theorem bind_pure_comp (f : α → β) (x : Prog es α) : bind 0 x (λ x ↦ pure (f x)) = map 1 f x :=
  x.rec (motive := λ n x ↦ match n with | 0 => True | n+1 => bind n x (λ x ↦ pure (f x)) = map (n + 1) f x)
    (λ _ ↦ True.intro)
    (λ {n} x h ↦ by
      cases n <;> dsimp
      simp only [bind_zero_varS, map_varS, map_zero]
      rfl
      simp only [bind_succ_varS, map_varS, map_zero]
      congr)
    (λ req res h ↦ by
      simp only [bind_op, map_op, op.injEq, heq_eq_eq, true_and]
      funext i
      exact h i)
    (λ req res h ↦ by
      simp only [bind_scope, map_scope, scope.injEq, heq_eq_eq, true_and]
      funext i
      exact h i)

theorem seq_def (f : Prog es (α → β)) (x : Prog es α) : f <*> x = bind 0 f λ y ↦ map 1 y x := by
  rfl

theorem seqLeft_def (x : Prog es α) (y : Prog es β) : x <* y = bind 0 x λ z ↦ bind 0 y (λ _ ↦ pure z) := by
  rfl

theorem seqRight_def (x : Prog es α) (y : Prog es β) : x *> y = bind 0 x λ _ ↦ y := by
  rfl

theorem seqLeft_eq (x : Prog es α) (y : Prog es β) : x <* y = (map 1 (Function.const _) x) <*> y := by
  rewrite [seq_def, seqLeft_def]
  apply x.rec
    (motive := λ n x ↦ match n with
      | 0 => True
      | n+1 => (bind n x λ z ↦ bind 0 y λ _ ↦ pure z) = bind n (map (n + 1) (Function.const β) x) λ z ↦ map 1 z y)
  · intro
    exact True.intro
  · intro n x h
    cases n <;> dsimp
    · rewrite [bind_zero_varS, map_varS, bind_zero_varS, map_zero, unwrap0_varZ]
      apply bind_pure_comp
    · rewrite [bind_succ_varS, map_varS, bind_succ_varS]
      congr
  · intro n req res h
    cases n <;> {
      dsimp
      rewrite [bind_op, map_op, bind_op]
      congr
      funext i
      exact h i
    }
  · intro n req res h
    cases n <;> {
      dsimp
      rewrite [bind_scope, map_scope, bind_scope]
      congr
      funext i
      exact h i
    }

theorem seqRight_eq (x : Prog es α) (y : Prog es β) : x *> y = (map 1 (Function.const _ id) x) <*> y := by
  rewrite [seq_def, seqRight_def]
  apply x.rec
    (motive := λ n x ↦ match n with
      | 0 => True
      | n+1 => (bind n x λ _ ↦ y) = bind n (map (n + 1) (Function.const α id) x) λ z ↦ map 1 z y)
  · intro
    exact True.intro
  · intro n x h
    cases n <;> dsimp
    · rw [
        map_varS, bind_zero_varS,
        map_zero, bind_zero_varS,
        unwrap0_varZ,
        Function.const_apply,
        map_id
      ]
    · rewrite [bind_succ_varS, map_varS, bind_succ_varS]
      congr
  · intro n req res h
    cases n <;> {
      dsimp
      rewrite [bind_op, map_op, bind_op]
      congr
      funext i
      exact h i
    }
  · intro n req res h
    cases n <;> {
      dsimp
      rewrite [bind_scope, map_scope, bind_scope]
      congr
      funext i
      exact h i
    }

end Prog'

instance : LawfulMonad (Prog es) where
  map_const := rfl
  pure_seq _ _ := rfl
  bind_map _ _ := rfl
  pure_bind _ _ := rfl
  id_map := Prog'.map_id
  seqLeft_eq := Prog'.seqLeft_eq
  seqRight_eq := Prog'.seqRight_eq
  bind_pure_comp := Prog'.bind_pure_comp
  bind_assoc := Prog'.bind_assoc
