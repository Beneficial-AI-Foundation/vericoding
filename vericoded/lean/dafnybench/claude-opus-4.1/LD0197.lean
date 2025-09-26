import Mathlib
-- <vc-preamble>
inductive Exp where
| Const : Int → Exp
| Var : String → Exp
| Plus : Exp → Exp → Exp
| Mult : Exp → Exp → Exp
deriving Repr

def eval (e : Exp) (store : String → Int) : Int :=
match e with
| Exp.Const n => n
| Exp.Var s => store s
| Exp.Plus e1 e2 => eval e1 store + eval e2 store
| Exp.Mult e1 e2 => eval e1 store * eval e2 store

def optimize (e : Exp) : Exp :=
match e with
| Exp.Mult (Exp.Const 0) _ => Exp.Const 0
| Exp.Mult _ (Exp.Const 0) => Exp.Const 0
| Exp.Mult (Exp.Const 1) e => e
| Exp.Mult e (Exp.Const 1) => e
| Exp.Mult (Exp.Const n1) (Exp.Const n2) => Exp.Const (n1 * n2)
| Exp.Plus (Exp.Const 0) e => e
| Exp.Plus e (Exp.Const 0) => e
| Exp.Plus (Exp.Const n1) (Exp.Const n2) => Exp.Const (n1 + n2)
| e => e
-- </vc-preamble>

-- <vc-helpers>

-- </vc-helpers>

-- <vc-definitions>
-- </vc-definitions>

-- <vc-theorems>
theorem optimizeCorrect (e : Exp) (s : String → Int) :
eval e s = eval (optimize e) s :=
by
  -- optimize only transforms the top-level structure, not sub-expressions
  -- We analyze e based on its top-level constructor
  unfold optimize
  split
  -- Case: Mult (Const 0) _
  · simp only [eval]
    ring
  -- Case: Mult _ (Const 0)
  · simp only [eval]
    ring
  -- Case: Mult (Const 1) e
  · simp only [eval]
    ring
  -- Case: Mult e (Const 1)
  · simp only [eval]
    ring
  -- Case: Mult (Const n1) (Const n2)
  · simp only [eval]
  -- Case: Plus (Const 0) e
  · simp only [eval]
    ring
  -- Case: Plus e (Const 0)
  · simp only [eval]
    ring
  -- Case: Plus (Const n1) (Const n2)
  · simp only [eval]
  -- Case: default (no optimization)
  · simp only [eval]
-- </vc-theorems>
