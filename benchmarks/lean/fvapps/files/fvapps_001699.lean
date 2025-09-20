-- <vc-preamble>
def List.noDuplicates (path : List Char) : Prop :=
  ∀ (x : Char), (List.count x path) ≤ 1

def List.isSorted (xs : List (List Char)) : Prop :=
  ∀ i j (h1 : i < j) (h2 : j < xs.length), (xs.get ⟨i, Nat.lt_trans h1 h2⟩) ≤ (xs.get ⟨j, h2⟩)

def Topology := Char → Char → Option Nat
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def shortestPath (G : Topology) (s e : Char) : List (List Char) :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem shortestPath_valid_paths {G : Topology} {s e : Char}
  (path : List Char) (h : path ∈ shortestPath G s e) :
    path.head? = some s ∧
    path.getLast? = some e ∧
    path.noDuplicates :=
sorry

theorem shortestPath_equal_length {G : Topology} {s e : Char}
  (p1 p2 : List Char) (h1 : p1 ∈ shortestPath G s e) (h2 : p2 ∈ shortestPath G s e) :
    p1.length = p2.length :=
sorry

theorem shortestPath_sorted {G : Topology} {s e : Char} :
  (shortestPath G s e).isSorted :=
sorry

theorem shortestPath_connected {G : Topology} {s e : Char}
  (path : List Char) (h : path ∈ shortestPath G s e) :
  ∀ i, i < path.length - 1 →
    ∃ h : i < path.length, ∃ h' : i + 1 < path.length,
      (G (path.get ⟨i, h⟩) (path.get ⟨i+1, h'⟩)).isSome :=
sorry

theorem shortestPath_disconnected {G : Topology} {s e : Char}
  (h_disconnected : ∀ c, (G s c).isNone) :
  shortestPath G s e = [] :=
sorry
-- </vc-theorems>