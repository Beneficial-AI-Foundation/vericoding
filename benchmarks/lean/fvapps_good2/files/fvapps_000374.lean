-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def min_malware_spread (graph : List (List Int)) (initial : List Int) : Int :=
sorry

def get_spread (graph : List (List Int)) (initial : List Int) (removed : Int) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem result_in_initial {graph : List (List Int)} {initial : List Int} :
  let result := min_malware_spread graph initial
  initial.contains result = true :=
sorry

theorem smallest_among_equal_spreads {graph : List (List Int)} {initial : List Int} :
  let result := min_malware_spread graph initial
  ∀ node : Int,
    node ∈ initial →
    node < result →
    get_spread graph initial node ≥ get_spread graph initial result :=
sorry

theorem valid_graph_properties {graph : List (List Int)} :
  let n := graph.length
  graph.length > 0 →
  (∀ row ∈ graph, row.length = n) →
  (∀ (i j : Nat), i < n → j < n →
    (graph.get! i).get! j = (graph.get! i).get! j) :=
sorry
-- </vc-theorems>