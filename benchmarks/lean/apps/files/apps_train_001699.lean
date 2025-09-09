def List.noDuplicates (path : List Char) : Prop := 
  ∀ (x : Char), (List.count x path) ≤ 1

def List.isSorted (xs : List (List Char)) : Prop :=
  ∀ i j, i < j → j < xs.length → (xs.get ⟨i, by sorry⟩) ≤ (xs.get ⟨j, by sorry⟩)

-- <vc-helpers>
-- </vc-helpers>

def Topology := Char → Char → Option Nat

def shortestPath (G : Topology) (s e : Char) : List (List Char) :=
sorry

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

/-
info: [['a', 'c', 'f'], ['a', 'e', 'f']]
-/
-- #guard_msgs in
-- #eval shortestPath {"a": {"b": 10, "c": 20, "e": 20}, "b": {"a": 10, "d": 20}, "c": {"a": 10, "f": 20}, "d": {"b": 10, "e": 20, "g": 20}, "e": {"a": 10, "d": 20, "f": 20}, "f": {"c": 10, "e": 20, "h": 20}, "g": {"d": 10, "h": 20}, "h": {"g": 10, "f": 20}} "a" "f"

/-
info: [['a', 'e']]
-/
-- #guard_msgs in
-- #eval shortestPath topology1 "a" "e"

/-
info: [['a', 'c']]
-/
-- #guard_msgs in
-- #eval shortestPath {"a": {"b": 10, "c": 20}, "b": {"a": 10, "c": 20}, "c": {"a": 10, "b": 20}} "a" "c"

-- Apps difficulty: interview
-- Assurance level: unguarded