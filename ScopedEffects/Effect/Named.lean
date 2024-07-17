import ScopedEffects.Prog

namespace ScopedEffects

variable {α : Type _} {e : Effect} {es : List Effect} {name : Lean.Name}

def Named (_name : Lean.Name) (e : Effect) : Effect where
  Operations := e.Operations
  Scopes := e.Scopes

@[inline]
def named'
  (name : Lean.Name)
  [mem : Mem (Named name e) es]
  {p : List Effect → Type}
  (h : p es)
  (x : ∀ {es'}, [Mem e es'] → p es' → Prog es' α)
  : Prog es α :=
    @x es mem h

@[inline]
def named
  (name : Lean.Name)
  [Mem (Named name e) es]
  (x : ∀ {es'}, [Mem e es'] → Prog es' α)
  : Prog es α :=
    named' (e := e) name (p := Function.const _ PUnit) .unit (λ _ ↦ x)
