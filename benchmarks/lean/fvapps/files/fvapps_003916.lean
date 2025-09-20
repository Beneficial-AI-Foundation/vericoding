-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def queue (queuers : List Nat) (pos : Nat) : Option Nat := sorry

theorem queue_basic_properties 
  (queuers : List Nat) (pos : Nat)
  (h1 : 0 < queuers.length) 
  (h2 : pos < queuers.length)
  (h3 : ∀ x ∈ queuers, 0 < x) :
  ∀ (result : Nat),
  queue queuers pos = some result →
  (result ≥ queuers[pos]'h2) 
  ∧ (result ≥ (List.range pos).foldl (λ sum i => 
      if h : i < queuers.length 
      then sum + min (queuers[i]'h) (queuers[pos]'h2)
      else sum) 0)
  ∧ (0 < result) := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem queue_first_position_capped
  (queuers : List Nat)
  (h1 : 0 < queuers.length)
  (h2 : ∀ x ∈ queuers, 0 < x) :
  let h3 : 0 < queuers.length := h1
  let capped := queuers.map (λ x => min x (queuers[0]'h3))
  queue queuers 0 = queue capped 0 := sorry

theorem queue_out_of_bounds
  (queuers : List Nat)
  (pos : Nat)
  (h1 : 0 < queuers.length)
  (h2 : queuers.length ≤ pos)
  (h3 : ∀ x ∈ queuers, 0 < x) :
  queue queuers pos = none := sorry
-- </vc-theorems>