-- <vc-preamble>
def Matrix := List String

def Query := Nat × Char
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def Result := String

def check_matrix_exists (L R : Nat) (matrix : Matrix) (queries : List Query) : List Result :=
  sorry

def all_same_matrix (c : Char) (L R : Nat) : Matrix :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem check_matrix_exists_results_match_queries
  (matrix : Matrix) (queries : List Query) (L R : Nat) :
  let results := check_matrix_exists L R matrix queries
  List.length results = List.length queries :=
sorry

theorem check_matrix_exists_valid_results
  (matrix : Matrix) (queries : List Query) (L R : Nat) :
  let results := check_matrix_exists L R matrix queries
  ∀ r ∈ results, r = "yes" ∨ r = "no" :=
sorry

theorem check_matrix_exists_size_constraint
  (matrix : Matrix) (queries : List Query) (L R : Nat) :
  let results := check_matrix_exists L R matrix queries
  ∀ (q : Query) (r : Result),
    (q, r) ∈ List.zip queries results →
    q.1 > min L R → r = "no" :=
sorry

theorem check_matrix_exists_all_same_char
  (matrix : Matrix) (queries : List Query) (L R : Nat) (c : Char) :
  let all_same := all_same_matrix c L R
  let results := check_matrix_exists L R all_same queries
  ∀ (q : Query) (r : Result),
    (q, r) ∈ List.zip queries results →
    (q.2 = c → r = "yes" ↔ q.1 ≤ min L R) ∧
    (q.2 ≠ c → r = "no") :=
sorry
-- </vc-theorems>