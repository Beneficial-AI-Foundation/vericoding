-- <vc-preamble>
def Operation := String × Int
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def DequeOp := List Operation

def splitString (s : String) : List String :=
  sorry

def process_deque_operations (ops : List String) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
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
-- </vc-theorems>