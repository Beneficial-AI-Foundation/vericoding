-- <vc-helpers>
-- </vc-helpers>

def Ticket := String × String

def findItinerary (tickets: List Ticket) : List String :=
  sorry

theorem findItinerary_starts_jfk (tickets: List Ticket) :
  (findItinerary tickets).head? = some "JFK" := sorry

theorem findItinerary_length (tickets: List Ticket) : 
  (findItinerary tickets).length = tickets.length + 1 := sorry

theorem findItinerary_valid_transitions (tickets: List Ticket) :
  let result := findItinerary tickets
  ∀ i, i < result.length - 1 → 
    (result[i]!, result[i+1]!) ∈ tickets := sorry 

theorem findItinerary_uses_all_tickets (tickets: List Ticket) :
  let result := findItinerary tickets
  let pairs := List.zip (result.take (result.length - 1)) (result.drop 1)
  pairs = tickets := sorry

/-
info: expected1
-/
-- #guard_msgs in
-- #eval findItinerary [["MUC", "LHR"], ["JFK", "MUC"], ["SFO", "SJC"], ["LHR", "SFO"]]

/-
info: expected2
-/
-- #guard_msgs in
-- #eval findItinerary [["JFK", "SFO"], ["JFK", "ATL"], ["SFO", "ATL"], ["ATL", "JFK"], ["ATL", "SFO"]]

-- Apps difficulty: interview
-- Assurance level: unguarded