-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def degree (node : Nat) (edges : List (Nat × Nat)) : Nat := sorry

def Tree (n : Nat) (edges : List (Nat × Nat)) : Prop :=
sorry

def sumOfDistancesInTree (n : Nat) (edges : List (Nat × Nat)) : List Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
def isLeafNode (node : Nat) (edges : List (Nat × Nat)) : Prop :=
  degree node edges = 1

theorem sumOfDistances_output_length
  (n : Nat) (edges : List (Nat × Nat)) :
  Tree n edges →
  List.length (sumOfDistancesInTree n edges) = n :=
sorry

theorem sumOfDistances_nonnegative
  (n : Nat) (edges : List (Nat × Nat))
  (i : Nat) (h : i < List.length (sumOfDistancesInTree n edges)) :
  Tree n edges →
  List.get! (sumOfDistancesInTree n edges) i ≥ 0 :=
sorry

theorem sumOfDistances_leaf_nodes_max
  (n : Nat) (edges : List (Nat × Nat))
  (node : Nat) (h : node < n) :
  Tree n edges →
  isLeafNode node edges →
  List.get! (sumOfDistancesInTree n edges) node ≤
    List.foldr max 0 (sumOfDistancesInTree n edges) :=
sorry
-- </vc-theorems>