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
  unfold optimize
  split <;> (intros; subst_vars; simp [eval, mul_comm, add_comm])
-- </vc-theorems>
