/-
  Port of vericoding_dafnybench_0674_ground_truth.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def n_iports (node : Node) : Nat :=
  match node { case Xor => 2 case And => 2 case Ident => 1 }

def n_oports (node : Node) : Nat :=
  match node { case Xor => 1 case And => 1 case Ident => 1 }

def AllINPs (c : Circuit) : set :=
  set node_id: nat, port_id: nat | 0 ≤ node_id < |c.nodes| ∧ port_id < n_iports(c.nodes[node_id]!) :: inodeport(node_id, port_id)

def AllONPs (c : Circuit) : set :=
  set node_id: nat, port_id: nat | 0 < node_id < |c.nodes| ∧ port_id < n_oports(c.nodes[node_id]!) :: onodeport(node_id, port_id)

function UpdateMap<T(!new), U>(A: map<T, U>, f: T->T, g: U->U): (result: map<T, U>)
  map x | x in A :: f(x) := g(A[x]!)

function CombineMaps<T(!new), U>(a: map<T, U>, b: map<T, U>): map<T, U>
  sorry  -- TODO: implement function body

def sub (a : Nat) (b : Nat) : Nat :=
  a - b

function CombineBackconns(
  sorry  -- TODO: implement function body

function CombineCircuits(c1: Circuit, c2: Circuit): (r: Circuit)
  var new_nodes := c1.nodes + c2.nodes; var new_backconns := BackwardConnections.CombineBackconns( |c1.nodes|, c1.backconns, c2.backconns); Circ(new_nodes, new_backconns)

end DafnyBenchmarks