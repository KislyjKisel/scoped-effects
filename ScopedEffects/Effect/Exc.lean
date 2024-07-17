import ScopedEffects.Prog

namespace ScopedEffects

variable {α ε : Type _} {es es' : List Effect}

inductive Exc.OperationsShape (ε : Type _) where
| throw (e : ε)

inductive Exc.ScopesShape where
| catch

inductive Exc.ScopesPosition (ε : Type _) where
| main
| handle (e : ε)

def Exc (ε : Type _) : Effect where
  Operations := ⟨Exc.OperationsShape ε, λ _ ↦ PEmpty⟩
  Scopes := ⟨Exc.ScopesShape, λ _ ↦ Exc.ScopesPosition ε⟩

@[inline]
def runExc (ε : Type _) : Prog (Exc ε :: es) α → Prog es (Except ε α) :=
  Prog'.foldP (λ n ↦ n.repeat (λ x ↦ Prog es (Except ε x)) α) 1
    id
    (λ a ↦ Prog'.pure (Except.ok a))
    (λ req res ↦
      match Prog.runAux (e := Exc ε) Effect.Operations ⟨req, res⟩ with
      | .inl ⟨.throw e, _⟩ => Prog'.pure (Except.error e)
      | .inr x => Prog'.op x.1 λ i ↦ x.2 i)
    (λ req res ↦
      match Prog.runAux (e := Exc ε) Effect.Scopes ⟨req, res⟩ with
      | .inl ⟨.catch, res⟩ =>
        Prog'.bind _ (res .main) λ
        | .ok x => x
        | .error e =>
          res (.handle e) >>= λ
          | .ok x => x
          | .error e => pure (.error e)
      | .inr x =>
        Prog'.scope x.1 λ i ↦
          Prog'.zip (m := 1) <| Prog'.map _
            (λ | .ok x => x | .error e => Prog'.pure (.error e))
            (x.2 i))

@[inline]
def throw [Mem (Exc ε) es] (e : ε) : Prog es α :=
  .mkOp (Exc ε) (.throw e) λ p ↦ nomatch p

@[inline]
def «catch» (ε : Type _) [Mem (Exc ε) es] (x : Prog es α) (f : ε → Prog es α) : Prog es α :=
  .mkScope (Exc ε) .catch λ
  | .main => Prog'.pure <$> x
  | .handle e => Prog'.pure <$> f e
