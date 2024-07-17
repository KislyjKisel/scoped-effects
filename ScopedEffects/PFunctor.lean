import Batteries.Data.Sum
import ScopedEffects.Data.List

namespace ScopedEffects

protected
structure PFunctor.{u} where
  Shape : Type u
  Position : Shape → Type u

namespace PFunctor

abbrev PFunctor := ScopedEffects.PFunctor

variable {α β : Type _} {c : PFunctor} {cs : List PFunctor}

def extension (c : PFunctor) (α : Type _) : Type _ :=
  Σ s : c.Shape, c.Position s → α

def map (f : α → β) (x : extension c α) : extension c β :=
  .mk x.fst λ i ↦ f (x.snd i)

instance : Functor (PFunctor.extension c) where
  map := c.map

def empty : PFunctor := .mk PEmpty PEmpty.elim

def lsum (cs : List PFunctor) : PFunctor :=
  ⟨Σ i : Fin cs.length, cs[i].Shape, λ ⟨i, s⟩ ↦ cs[i].Position s⟩

def mkLsum (i : Fin cs.length) (x : cs[i].extension α) : (lsum cs).extension α :=
  ⟨⟨i, x.1⟩, x.2⟩

@[always_inline]
def lsum_zero {c} {cs : List PFunctor} (x : (lsum (c :: cs)).extension α) (h : x.1.1.1 = 0) : c.extension α := by
  match x with
  | ⟨⟨⟨0, _⟩, req⟩, res⟩ =>
    exact ⟨req, res⟩
  | ⟨⟨⟨n+1, _⟩, _⟩, _⟩ =>
    contradiction

@[always_inline]
def lsum_eq {c} {cs : List PFunctor} (x : (lsum cs).extension α) (h : cs[x.1.1.1] = c) : c.extension α := by
  simp only [← h]
  exact ⟨x.1.2, x.2⟩

@[always_inline]
def lsum_ne (x : (lsum cs).extension α) (i : Fin cs.length) (h : x.1.1.1 ≠ i) : (lsum (List.eraseIdx cs i)).extension α := by
  apply dite (x.1.1.1 < i) <;> intro h'
  case t =>
    have x_lt_cs' : x.1.1.1 < (cs.eraseIdx i).length := by
      rewrite [List.length_eraseIdx i.2]
      apply Nat.lt_of_lt_of_le h' (Nat.le_pred_of_lt i.2)
    apply mkLsum ⟨x.1.1.1, x_lt_cs'⟩
    rewrite [Fin.getElem_fin, ScopedEffects.getElem_eraseIdx_lt (i := x.fst.fst) (j := i.1) h' i.2]
    exact ⟨x.1.2, x.2⟩
  case e =>
    have x_gt_i : x.1.1.1 > i := by
      cases Nat.le_iff_lt_or_eq.mp (Nat.le_of_not_gt h')
      case inl => assumption
      case inr h => have h := h.symm; contradiction
    have : x.1.1.1 - 1 < (cs.eraseIdx i).length := by
      rewrite [List.length_eraseIdx i.2]
      apply Nat.pred_lt_pred _ x.1.1.2
      exact Nat.not_eq_zero_of_lt x_gt_i
    apply mkLsum ⟨x.1.1.1 - 1, this⟩
    rewrite [Fin.getElem_fin, ScopedEffects.getElem_eraseIdx_gt x_gt_i x.1.1.2 i.2]
    exact ⟨x.1.2, x.2⟩

@[always_inline]
def lsum_succ {c} {cs : List PFunctor} (x : (lsum (c :: cs)).extension α) (h : x.1.1.1 > 0) : (lsum cs).extension α := by
  match x with
  | ⟨⟨⟨0, _⟩, req⟩, res⟩ =>
    contradiction
  | ⟨⟨⟨n+1, h⟩, req⟩, res⟩ =>
    refine ⟨⟨⟨n, ?_⟩, req⟩, res⟩
    rewrite [List.length_cons] at h
    exact Nat.lt_of_succ_lt_succ h
