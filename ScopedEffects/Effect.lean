import ScopedEffects.PFunctor

namespace ScopedEffects

structure Effect.{u} where
  Operations : ScopedEffects.PFunctor.{u}
  Scopes : ScopedEffects.PFunctor.{u}

variable {α : Type _}
  {c : ScopedEffects.PFunctor} {cs : List ScopedEffects.PFunctor}
  {e e' : Effect} {es es' : List Effect}

def Effect.operations : List Effect → ScopedEffects.PFunctor :=
  .lsum ∘ List.map Operations

def Effect.scopes : List Effect → ScopedEffects.PFunctor :=
  .lsum ∘ List.map Scopes

class Mem (e : Effect) (es : List Effect) where
  index : Fin es.length
  eq : es[index.1] = e

instance Mem.instHere (e es) : Mem e (e :: es) := by
  refine ⟨⟨0, ?_⟩, ?_⟩
  rewrite [List.length_cons]
  exact Nat.zero_lt_succ _
  rw [List.getElem_cons_zero]

instance Mem.instThere (e e' es) [h: Mem e es] : Mem e (e' :: es) := by
  refine ⟨⟨h.1 + 1, ?_⟩, ?_⟩
  rewrite [List.length_cons]
  apply Nat.add_lt_add_right
  exact h.1.2
  rewrite [List.getElem_cons_succ]
  exact h.2

@[always_inline]
def Effect.inj [mem : Mem e es] (ec : Effect → ScopedEffects.PFunctor) (x : (ec e).extension α) :
  (PFunctor.lsum <| es.map ec).extension α := by
    let i : Fin (es.map ec).length := Fin.mk mem.1 $ by
      rewrite [List.length_map]
      exact mem.1.2
    have : Σ i : Fin (es.map ec).length, PLift ((es.map ec)[i] = ec e) := by
      apply Sigma.mk i ∘ .up
      show (es.map ec)[i] = (ec e)
      have : es[mem.1] = e := mem.2
      rewrite [Fin.getElem_fin, List.getElem_map, ← this]
      rfl
    let x := this.2.down.symm ▸ x
    exact ⟨⟨this.1, x.1⟩, x.2⟩
