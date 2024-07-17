import ScopedEffects.Prog
import ScopedEffects.Prog.Lawful
import ScopedEffects.Effect.State
import ScopedEffects.Effect.Exc
import ScopedEffects.Effect.Reader
import ScopedEffects.Effect.Writer

-- open ScopedEffects

-- variable {es : List Effect}

-- def test
--   [Mem (Reader Nat) es]
--   [Mem (State Nat) es]
--   [Mem (Writer (List Nat)) es]
--   [Mem (Exc String) es]
--   : Prog es Nat := do
--     let x ← get Nat
--     let y := x + 1
--     tell [0]
--     «censor» (ω := List Nat) (λ x ↦ x.concat 10) do
--       «catch» String
--         (do
--           set 0
--           tell [1]
--           throw "err1")
--         (λ s ↦ do
--           «local» (λ x ↦ x + 1) do
--             set (← ask Nat)
--           tell [2]
--           throw "err2")
--     tell [3]
--     pure y

-- #eval ScopedEffects.Prog.run <|
--   runReader 100 <|
--   runState 0 <|
--   runWriter (ω := List Nat) [] .append <|
--   runExc String <|
--   test
