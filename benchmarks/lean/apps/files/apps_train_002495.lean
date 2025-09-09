def Operation := String × Int
def DequeOp := List Operation

def splitString (s : String) : List String :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

def process_deque_operations (ops : List String) : String :=
  sorry

theorem append_only_operations_preserves_length 
  (ops : List String)
  (h1 : ∀ op ∈ ops, (splitString op).get! 0 = "append" ∨ (splitString op).get! 0 = "appendleft") :
  (splitString (process_deque_operations ops)).length = ops.length :=
  sorry

theorem append_only_operations_preserves_elements
  (ops : List String)
  (h1 : ∀ op ∈ ops, (splitString op).get! 0 = "append" ∨ (splitString op).get! 0 = "appendleft") :
  ∃ perm : List String → List String, 
    perm (ops.map (λ op => (splitString op).get! 1)) = 
    splitString (process_deque_operations ops) :=
  sorry

theorem append_maintains_order
  (ops : List String)
  (h1 : ∀ op ∈ ops, (splitString op).get! 0 = "append") :
  (splitString (process_deque_operations ops)) =
  ops.map (λ op => (splitString op).get! 1) :=
  sorry

/-
info: '1 2'
-/
-- #guard_msgs in
-- #eval process_deque_operations ["append 1", "append 2", "append 3", "appendleft 4", "pop", "popleft"]

/-
info: '10 15'
-/
-- #guard_msgs in
-- #eval process_deque_operations ["append 5", "appendleft 10", "pop", "append 15"]

/-
info: ''
-/
-- #guard_msgs in
-- #eval process_deque_operations ["append 1", "appendleft 2", "popleft", "pop"]

-- Apps difficulty: introductory
-- Assurance level: unguarded