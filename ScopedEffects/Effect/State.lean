import ScopedEffects.Prog

namespace ScopedEffects

universe u
variable {α σ : Type} {es es' : List Effect}

inductive State.OperationsShape (σ : Type u) : Type u where
| get
| set (value : σ)

def State.OperationsPosition {σ : Type u} : OperationsShape σ → Type u
| .get => σ
| .set _ => PUnit

def State (σ : Type u) : Effect.{u} where
  Operations := ⟨State.OperationsShape σ, State.OperationsPosition⟩
  Scopes := .empty

@[inline]
def runState (s : σ) (x : Prog (State σ :: es) α) : Prog es (α × σ) :=
  let f :=
    Prog'.foldP (λ n ↦ n.repeat (λ x ↦ σ → Prog es (x × σ)) α) 1
      id
      (λ a s ↦ pure (a, s))
      (λ req res s ↦
        match Prog.runAux (e := State σ) Effect.Operations ⟨req, res⟩ with
        | .inl x =>
          match x with
          | ⟨.get, res⟩ => res s s
          | ⟨.set s, res⟩ => res PUnit.unit s
        | .inr x =>
          .op x.1 λ i ↦ x.2 i s)
      (λ req res s ↦
        match Prog.runAux (e := State σ) Effect.Scopes ⟨req, res⟩ with
        | .inr x =>
          .scope (n := 0) x.1 λ i ↦ Prog'.zip (m := 1) <| (λ (f, s) ↦ f s) <$> (x.2 i s))
  f x s

@[inline]
def get (σ : Type _) [Mem (State σ) es] : Prog es σ :=
  .mkOp (State σ) .get pure

@[inline]
def set [Mem (State σ) es] (value : σ) : Prog es PUnit :=
  .mkOp (State σ) (.set value) pure
