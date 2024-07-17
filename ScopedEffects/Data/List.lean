import Batteries.Data.List.Lemmas

namespace ScopedEffects

variable {α β : Type _}

protected
theorem getElem_eraseIdx_lt {xs : List α} {i j} (h₁ : i < j) (h₂ : j < xs.length) :
  (xs.eraseIdx j)[i]'(
    by rw [List.length_eraseIdx h₂]; exact Nat.lt_of_lt_of_le h₁ (Nat.le_pred_of_lt h₂)
  ) = xs[i] := by
    cases xs
    rfl
    cases i
    · rewrite [List.getElem_cons_zero]
      cases j
      · contradiction
      · simp only [List.eraseIdx_cons_succ]
        apply List.getElem_cons_zero
    · rewrite [List.getElem_cons_succ]
      cases j
      · contradiction
      · simp only [List.eraseIdx_cons_succ, List.getElem_cons_succ]
        apply ScopedEffects.getElem_eraseIdx_lt
        exact Nat.lt_of_succ_lt_succ h₁
        rewrite [List.length_cons] at h₂
        exact Nat.lt_of_succ_lt_succ h₂

protected
theorem getElem_eraseIdx_gt {xs : List α} {i j} (h₁ : i > j) (h₂ : i < xs.length) (h₃ : j < xs.length) :
  (xs.eraseIdx j)[i - 1]'(
    by rw [List.length_eraseIdx h₃]; apply Nat.pred_lt_pred (Nat.not_eq_zero_of_lt h₁) h₂
  ) = xs[i] := by
    sorry

protected
theorem map_eraseIdx {xs : List α} {f : α → β} {i} : (xs.eraseIdx i).map f = (xs.map f).eraseIdx i := by
  cases xs
  rfl
  cases i
  rfl
  rewrite [List.eraseIdx_cons_succ, List.map_cons, List.map_cons, List.eraseIdx_cons_succ]
  congr
  exact ScopedEffects.map_eraseIdx
