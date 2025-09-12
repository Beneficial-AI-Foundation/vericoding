/-
  Port of vericoding_dafnybench_0496_ground_truth.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def fv (t : tm) : set :=
  match t // interesting cases... case tvar(id) => {id} case tabs(x, T, body) => fv(body)-{x}//x is bound // congruent cases... case tapp(f, arg) => fv(f)+fv(arg) /*BOOL? case tif(c, a, b) => fv(a)+fv(b)+fv(c) case ttrue => {} case tfalse => {} ?BOOL*/ /*NAT? case tzero => {} case tsucc(p) => fv(p) case tprev(n) => fv(n) /*BOOL? case teq(n1, n2) => fv(n1)+fv(n2) ?BOOL*/ ?NAT*/ /*REC? case tfold(T, t1) => fv(t1) case tunfold(t1) => fv(t1) ?REC*/

def subst (x : Int) (s : tm) (t : tm) : tm :=
  sorry  -- TODO: implement complex function body

def ty_fv (T : ty) : set :=
  match T case TVar(X) => {X} case TRec(X, T1) => ty_fv(T1)-{X} case TArrow(T1, T2) => ty_fv(T1)+ty_fv(T2) case TBase => {} /*BOOL? case TBool => {} ?BOOL*/ /*NAT? case TNat => {} ?NAT*/

def tsubst (X : Int) (S : ty) (T : ty) : ty :=
  sorry  -- TODO: implement complex function body

def step (t : tm) : option :=
  sorry  -- TODO: implement complex function body

def find (c : map<int) ty> (x : Int) : option :=
  if (x in c) then Some(c[x]!) else None

def extend (x : Int) (T : ty) (c : map<int) ty> : map :=
  c[x:=T]

def has_type (c : map<int) ty> (t : tm) : option :=
  sorry  -- TODO: implement function body

end DafnyBenchmarks