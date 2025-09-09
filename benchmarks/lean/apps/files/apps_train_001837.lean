/-
Given a list of airline tickets represented by pairs of departure and arrival airports [from, to], reconstruct the itinerary in order. All of the tickets belong to a man who departs from JFK. Thus, the itinerary must begin with JFK.

Note:

       If there are multiple valid itineraries, you should return the itinerary that has the smallest lexical order when read as a single string. For example, the itinerary ["JFK", "LGA"] has a smaller lexical order than ["JFK", "LGB"].
       All airports are represented by three capital letters (IATA code).
       You may assume all tickets form at least one valid itinerary.

Example 1:

Input: tickets = [["MUC", "LHR"], ["JFK", "MUC"], ["SFO", "SJC"], ["LHR", "SFO"]]
Output: ["JFK", "MUC", "LHR", "SFO", "SJC"]

Example 2:

Input: tickets = [["JFK","SFO"],["JFK","ATL"],["SFO","ATL"],["ATL","JFK"],["ATL","SFO"]]
Output: ["JFK","ATL","JFK","SFO","ATL","SFO"]
Explanation: Another possible reconstruction is ["JFK","SFO","ATL","JFK","ATL","SFO"]. But it is larger in lexical order.

Credits:
Special thanks to @dietpepsi for adding this problem and creating all test cases.
-/

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