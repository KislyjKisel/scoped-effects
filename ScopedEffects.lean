import ScopedEffects.Prog
import ScopedEffects.Prog.Lawful
import ScopedEffects.Effect.State
import ScopedEffects.Effect.Exc
import ScopedEffects.Effect.Reader

open ScopedEffects

-- variable {es : List Effect}

-- def test
--   [Mem (Reader Nat) es]
--   [Mem (State Nat) es]
--   [Mem (State String) es]
--   [Mem (Exc String) es]
--   : Prog es Nat := do
--     let x ← get Nat
--     let y := x + 1
--     «catch» String
--       (do
--         set 0
--         throw "err1"
--         set "unreachable")
--       (λ s ↦ do
--         let x ← get (σ := String)
--         «local» (λ x ↦ x + 1) do
--           set (← ask Nat)
--         set <| s ++ toString (← ask Nat)
--         throw x)
--     pure y

-- #eval ScopedEffects.Prog.run <|
--   runReader 100 <|
--   runState 0 <|
--   runState "initial" <|
--   runExc String <|
--   test
