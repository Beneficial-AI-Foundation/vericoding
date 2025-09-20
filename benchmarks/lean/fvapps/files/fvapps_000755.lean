-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def absolute_value (x : Int) : Int := if x ≥ 0 then x else -x

def can_frogs_communicate (n : Nat) (k : Int) (coords : List Int) (pairs : List (Nat × Nat)) : List String := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem can_frogs_communicate_output_format 
  {n : Nat} {k : Int} {coords : List Int} {pairs : List (Nat × Nat)}
  (h1 : n ≥ 2)
  (h2 : coords.length = n)
  (h3 : coords.Nodup)
  (h4 : pairs.length > 0) :
  let result := can_frogs_communicate n k coords pairs
  result.length = pairs.length ∧ 
  ∀ x, x ∈ result → x = "Yes" ∨ x = "No" := sorry

theorem can_frogs_communicate_reflexive
  {n : Nat} {k : Int} {coords : List Int}
  (h1 : n ≥ 2)
  (h2 : coords.length = n)
  (h3 : coords.Nodup) :
  let same_pairs := List.map (fun i => (i+1, i+1)) (List.range n)
  let result := can_frogs_communicate n k coords same_pairs
  ∀ x, x ∈ result → x = "Yes" := sorry

theorem can_frogs_communicate_distance
  {n : Nat} {k : Int} {coords : List Int} {pairs : List (Nat × Nat)}
  (h1 : n ≥ 2)
  (h2 : coords.length = n)
  (h3 : coords.Nodup)
  (h4 : pairs.length > 0) :
  let result := can_frogs_communicate n k coords pairs
  ∀ (i : Nat), i < pairs.length →
    result[i]! = "Yes" →
    ∀ x y, x ∈ coords → y ∈ coords →
      x ≥ min (coords[pairs[i]!.1-1]!) (coords[pairs[i]!.2-1]!) →
      y ≤ max (coords[pairs[i]!.1-1]!) (coords[pairs[i]!.2-1]!) →
      absolute_value (x - y) ≤ k := sorry

theorem can_frogs_communicate_symmetric 
  {n : Nat} {k : Int} {coords : List Int} {pairs : List (Nat × Nat)}
  (h1 : n ≥ 2)
  (h2 : coords.length = n)
  (h3 : coords.Nodup)
  (h4 : pairs.length > 0) :
  let reverse_pairs := pairs.map (fun p => (p.2, p.1))
  can_frogs_communicate n k coords pairs = 
  can_frogs_communicate n k coords reverse_pairs := sorry
-- </vc-theorems>