import ScopedEffects.Effect

namespace ScopedEffects

variable {α β : Type _} {e : Effect} {es : List Effect}

protected
inductive Prog'.{u} (es : List Effect.{u}) (α : Type u) : Nat → Type u where
| varZ (x : α) : ScopedEffects.Prog' es α 0
| varS {n} (x : ScopedEffects.Prog' es α n) : ScopedEffects.Prog' es α (n + 1)
| op {n} (s : (Effect.operations es).Shape) (x : (Effect.operations es).Position s → ScopedEffects.Prog' es α (n + 1)) : ScopedEffects.Prog' es α (n + 1)
| scope {n} (s : (Effect.scopes es).Shape) (x : (Effect.scopes es).Position s → ScopedEffects.Prog' es α (n + 2)) : ScopedEffects.Prog' es α (n + 1)

abbrev Prog'.Prog' := ScopedEffects.Prog'

abbrev Prog (es) (α) := ScopedEffects.Prog' es α 1

namespace Prog'

@[inline]
def unwrap0 : Prog' es α 0 → α
| .varZ x => x

def unzip {n m k} : Prog' es α n → n = k + m + 1 → Prog' es (Prog' es α k) (m + 1)
| .varS x, h =>
  match m with
  | 0 => by
    cases h
    exact Prog'.varS <| Prog'.varZ x
  | _+1 =>
    .varS <| x.unzip <| Nat.succ_inj'.mp h
| .op req res, h =>
  .op req λ i ↦ (res i).unzip h
| .scope req res, h =>
  .scope req λ i ↦ (res i).unzip (Nat.succ_inj'.mpr h)

def zip {m n} : Prog' es (Prog' es α m) n → Prog' es α (m+n)
| .varZ x => x
| .varS x => .varS x.zip
| .op req res => .op req λ i ↦ (res i).zip
| .scope req res => .scope req λ i ↦ (res i).zip

abbrev foldP.OpF (es) (p : Nat → Type) :=
  ∀ {n : Nat}, (s : (Effect.operations es).Shape) → ((Effect.operations es).Position s → (p n.succ)) → p n.succ

abbrev foldP.ScopeF (es) (p : Nat → Type) :=
  ∀ {n : Nat}, (s : (Effect.scopes es).Shape) → ((Effect.scopes es).Position s → (p n.succ.succ)) → p n.succ

@[specialize]
def foldP (p : Nat → Type) (n)
  (a : α → p 0)
  (v : ∀ {n : Nat}, p n → p n.succ)
  (o : foldP.OpF es p)
  (s : foldP.ScopeF es p)
  (x : Prog' es α n)
  : p n :=
    match n, x with
    | 0, .varZ x => a x
    | n+1, .varS x => v <| foldP p n a v o s x
    | n+1, .op req res => o req λ i ↦ foldP p n.succ a v o s (res i)
    | n+1, .scope req res => s req λ i ↦ foldP p n.succ.succ a v o s (res i)

@[inline]
def map (n) (f : α → β) (x : Prog' es α n) : Prog' es β n :=
  foldP _ n (Prog'.varZ ∘ f) Prog'.varS op scope x

abbrev bindP (es : List Effect) (β : Type _) : Nat → Type _
| 0 => Prog es β
| n+1 => Prog' es β n.succ

def bindVar : (n : Nat) → bindP es β n → bindP es β n.succ
| 0, x => x
| _+1, x => Prog'.varS x

def bind (n) (x : Prog' es α (n + 1)) (f : α → Prog es β) : Prog' es β (n + 1) :=
  foldP (bindP es β) n.succ f (λ {n} ↦ bindVar n) op scope x

@[inline]
def pure : α → Prog es α :=
  varS ∘ varZ

@[specialize]
def mkScope (e : Effect) [Mem e es] (req : e.Scopes.Shape) (res : e.Scopes.Position req → Prog' es α 2) : Prog es α :=
  let ⟨req, res⟩ := Effect.inj Effect.Scopes ⟨req, res⟩
  scope req res

end Prog'

namespace Prog

def run : Prog [] α → α
| .varS (.varZ x) => x

instance : Monad (Prog es) where
  pure := Prog'.pure
  map := Prog'.map 1
  bind := Prog'.bind 0

@[specialize]
def mkOp (e : Effect) [Mem e es] (req : e.Operations.Shape) (res : e.Operations.Position req → Prog es α) : Prog es α :=
  let ⟨req, res⟩ := Effect.inj Effect.Operations ⟨req, res⟩
  Prog'.op req res

@[inline]
def mkScope (e : Effect) [Mem e es] (req : e.Scopes.Shape) (res : e.Scopes.Position req → Prog es (Prog es α)) : Prog es α :=
  Prog'.mkScope e req λ i ↦ (res i).zip

@[inline]
def runAux (ec : Effect → ScopedEffects.PFunctor) (c : (PFunctor.lsum <| List.map ec <| (e :: es)).extension α) :
  Sum ((ec e).extension α) ((PFunctor.lsum <| List.map ec <| es).extension α) := by
    rewrite [List.map_cons] at c
    apply dite (c.1.1.1 = 0) <;> intro h
    case t =>
      apply Sum.inl
      apply PFunctor.lsum_zero c h
    case e =>
      apply Sum.inr
      apply PFunctor.lsum_succ c (Nat.pos_of_ne_zero h)

@[inline]
def runAux' [mem : Mem e es] (ec : Effect → ScopedEffects.PFunctor) (c : (PFunctor.lsum <| List.map ec <| es).extension α) :
  Sum ((ec e).extension α) ((PFunctor.lsum <| List.map ec <| List.eraseIdx es mem.index).extension α) := by
    apply dite (c.1.1.1 = mem.index) <;> intro h
    case t =>
      apply Sum.inl
      apply PFunctor.lsum_eq c
      simp only [h, List.getElem_map, mem.eq]
    case e =>
      apply Sum.inr
      rewrite [ScopedEffects.map_eraseIdx]
      apply PFunctor.lsum_ne (i := ⟨mem.index, _⟩) c h
      rewrite [List.length_map]
      exact mem.index.2

end Prog
