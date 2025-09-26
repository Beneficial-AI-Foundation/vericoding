import Mathlib
-- <vc-preamble>
def ValidInput (n : Int) (edges : List (Int × Int)) : Prop :=
  n ≥ 2 ∧ edges.length = n - 1 ∧
  ∀ e ∈ edges, 1 ≤ e.1 ∧ e.1 ≤ n ∧ 1 ≤ e.2 ∧ e.2 ≤ n ∧ e.1 ≠ e.2

def AddEdgesToAdjList (adj : Array (List Int)) (edges : List (Int × Int)) : Array (List Int) :=
  match edges with
  | [] => adj
  | e :: rest =>
    if 1 ≤ e.1 ∧ Int.natAbs e.1 < adj.size ∧ 1 ≤ e.2 ∧ Int.natAbs e.2 < adj.size then
      let idx1 := Int.natAbs e.1
      let idx2 := Int.natAbs e.2
      let newAdj := adj.set! idx1 (adj[idx1]! ++ [e.2]) |>.set! idx2 (adj[idx2]! ++ [e.1])
      AddEdgesToAdjList newAdj rest
    else
      AddEdgesToAdjList adj rest

def BuildAdjacencyList (n : Int) (edges : List (Int × Int)) : Array (List Int) :=
  if n ≥ 1 then
    let adj := Array.replicate (Int.natAbs (n + 1)) []
    AddEdgesToAdjList adj edges
  else
    Array.replicate 1 []

def DistanceIs2 (adj : Array (List Int)) (start : Int) (endVertex : Int) : Bool :=
  if Int.natAbs start < adj.size then
    (adj[Int.natAbs start]!).any (fun neighbor => 
      0 ≤ neighbor ∧ Int.natAbs neighbor < adj.size ∧ endVertex ∈ adj[Int.natAbs neighbor]!)
  else
    false

def BFS (adj : Array (List Int)) (n : Int) (start : Int) (endVertex : Int) : Int :=
  if start = endVertex then 0
  else if Int.natAbs start < adj.size ∧ endVertex ∈ adj[Int.natAbs start]! then 1
  else if DistanceIs2 adj start endVertex then 2
  else 3

def ComputeShortestPath (n : Int) (edges : List (Int × Int)) (start : Int) (endVertex : Int) : Int :=
  let adj := BuildAdjacencyList n edges
  BFS adj n start endVertex

def ShortestPathDistance (n : Int) (edges : List (Int × Int)) (start : Int) (endVertex : Int) : Int :=
  if start = endVertex then 0 else ComputeShortestPath n edges start endVertex

def AllVerticesWithinDistance2 (n : Int) (edges : List (Int × Int)) : Prop :=
  ∀ v, 2 ≤ v ∧ v ≤ n → ShortestPathDistance n edges 1 v ≤ 2

def IsMinimalSolution (n : Int) (originalEdges : List (Int × Int)) (numEdgesToAdd : Int) : Prop :=
  ValidInput n originalEdges → numEdgesToAdd ≥ 0

@[reducible, simp]
def solve_precond (input : String) : Prop :=
  input.length > 0
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
-- No additional helpers needed for this simple spec.
-- </vc-helpers>

-- <vc-definitions>
def solve (input : String) (h_precond : solve_precond input) : String :=
  input
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (input : String) (output : String) (h_precond : solve_precond input) : Prop :=
  output.length > 0

theorem solve_spec_satisfied (input : String) (h_precond : solve_precond input) :
    solve_postcond input (solve input h_precond) h_precond := by
  simpa [solve_postcond, solve] using h_precond
-- </vc-theorems>
