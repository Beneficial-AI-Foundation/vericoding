-- <vc-preamble>
def Segment := Int × Int 

inductive Operation
  | L_plus
  | L_minus
  | R_plus 
  | R_minus

def apply_operation (s : Segment) (op : Operation) : Segment :=
  match op with
  | Operation.L_plus => (s.1 + 1, s.2)
  | Operation.L_minus => (s.1 - 1, s.2) 
  | Operation.R_plus => (s.1, s.2 + 1)
  | Operation.R_minus => (s.1, s.2 - 1)

def is_valid_segment (s : Segment) : Bool :=
  s.1 < s.2
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (segments : List Segment) : List Operation := sorry

theorem operations_preserve_validity 
  (segments : List Segment)
  (h₁ : segments ≠ [])
  (h₂ : ∀ s ∈ segments, is_valid_segment s = true) :
  let ops := solve segments
  ∀ i, i ≤ ops.length →
  let curr := List.foldl apply_operation (List.head segments h₁) (ops.take i)
  is_valid_segment curr = true :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem reaches_target_segments
  (segments : List Segment)
  (h₁ : segments ≠ [])
  (h₂ : ∀ s ∈ segments, is_valid_segment s = true) :
  let ops := solve segments
  ∀ target ∈ segments.tail,
  ∃ i ≤ ops.length,
  List.foldl apply_operation (List.head segments h₁) (ops.take i) = target :=
sorry
-- </vc-theorems>