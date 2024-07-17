import ScopedEffects.Prog

namespace ScopedEffects

variable {α ω : Type} {es es' : List Effect}

inductive Writer.OperationsShape (ω : Type _) where
| tell (x : ω)

def Writer.OperationsPosition : OperationsShape ω → Type _
| .tell _ => PUnit

inductive Writer.ScopesShape (ω : Type _) where
| censor (f : ω → ω)

def Writer.ScopesPosition : ScopesShape ω → Type _
| .censor _ => PUnit

def Writer (ω : Type _) : Effect where
  Operations := ⟨Writer.OperationsShape ω, Writer.OperationsPosition⟩
  Scopes := ⟨Writer.ScopesShape ω, Writer.ScopesPosition⟩

@[inline]
def runWriter (empty : ω) (append : ω → ω → ω) (x : Prog (Writer ω :: es) α) : Prog es (α × ω) :=
  let f :=
    Prog'.foldP (λ n ↦ n.repeat (λ x ↦ ω → Prog es (x × ω)) α) 1
      id
      (λ a s ↦ Prog'.pure (a, s))
      (λ req res s ↦
        match Prog.runAux (e := Writer ω) Effect.Operations ⟨req, res⟩ with
        | .inl ⟨.tell s', res⟩ => res .unit (append s s')
        | .inr x => Prog'.op x.1 λ i ↦ x.2 i s)
      (λ req res s ↦
        match Prog.runAux (e := Writer ω) Effect.Scopes ⟨req, res⟩ with
        | .inl ⟨.censor f, res⟩ =>
          Prog'.bind _ (res .unit empty) λ (x, s') ↦ x <| append s (f s')
        | .inr x =>
          Prog'.scope x.1 λ i ↦
            Prog'.zip (m := 1) <| Prog'.map _ (λ | (f, x) => f x) (x.2 i s))
  f x empty

@[inline]
def tell [Mem (Writer ω) es] (value : ω) : Prog es PUnit :=
  .mkOp (Writer ω) (.tell value) pure

@[inline]
def censor [Mem (Writer ω) es] (f : ω → ω) (x : Prog es α) : Prog es α :=
  .mkScope (Writer ω) (.censor f) λ _ ↦ Prog'.pure <$> x
