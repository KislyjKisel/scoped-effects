import ScopedEffects.Prog
import ScopedEffects.Effect.Named

namespace ScopedEffects

variable {α ρ : Type} {es es' : List Effect}

inductive Reader.OperationsShape where
| ask

def Reader.OperationsPosition (ρ : Type _) : OperationsShape → Type _
| .ask => ρ

inductive Reader.ScopesShape (ρ : Type _) where
| local (f : ρ → ρ)

def Reader.ScopesPosition : ScopesShape ρ → Type _
| .local _ => PUnit

def Reader (ρ : Type _) : Effect where
  Operations := ⟨Reader.OperationsShape, Reader.OperationsPosition ρ⟩
  Scopes := ⟨Reader.ScopesShape ρ, Reader.ScopesPosition⟩

@[inline]
def runReader (r : ρ) (x : Prog (Reader ρ :: es) α) : Prog es α :=
  let f :=
    Prog'.foldP (λ n ↦ n.repeat (λ x ↦ ρ → Prog es x) α) 1
      id
      (λ a _ ↦ Prog'.pure a)
      (λ req res r ↦
        match Prog.runAux (e := Reader ρ) Effect.Operations ⟨req, res⟩ with
        | .inl ⟨.ask, res⟩ => res r r
        | .inr x => Prog'.op x.1 λ i ↦ x.2 i r)
      (λ req res r ↦
        match Prog.runAux (e := Reader ρ) Effect.Scopes ⟨req, res⟩ with
        | .inl ⟨.local f, res⟩ =>
          Prog'.bind _ (res .unit (f r)) λ x ↦ x r
        | .inr x =>
          Prog'.scope x.1 λ i ↦
            Prog'.zip (m := 1) <| Prog'.map _ (λ | x => x r) (x.2 i r))
  f x r

@[inline]
def runReaderNamed (name : Lean.Name) (r : ρ) (x : Prog (Named name (Reader ρ) :: es) α) : Prog es α :=
  runReader r x

@[inline]
def ask (ρ : Type _) [Mem (Reader ρ) es] : Prog es ρ :=
  .mkOp (Reader ρ) .ask pure

@[inline]
def «local» [Mem (Reader ρ) es] (f : ρ → ρ) (x : Prog es α) : Prog es α :=
  .mkScope (Reader ρ) (.local f) λ _ ↦ Prog'.pure <$> x
