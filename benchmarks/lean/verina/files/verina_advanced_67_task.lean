-- <vc-preamble>
@[reducible, simp]
def runLengthEncode_precond (s : String) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def runLengthEncode (s : String) (h_precond : runLengthEncode_precond (s)) : List (Char × Nat) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
def decodeRLE (lst : List (Char × Nat)) : String :=
  match lst with
  | [] => ""
  | (ch, cnt) :: tail =>
    let repeated := String.mk (List.replicate cnt ch)
    repeated ++ decodeRLE tail
@[reducible, simp]
def runLengthEncode_postcond (s : String) (result: List (Char × Nat)) (h_precond : runLengthEncode_precond (s)) : Prop :=
  (∀ pair ∈ result, pair.snd > 0) ∧
  (∀ i : Nat, i < result.length - 1 → (result[i]!).fst ≠ (result[i+1]!).fst) ∧
  decodeRLE result = s

theorem runLengthEncode_spec_satisfied (s: String) (h_precond : runLengthEncode_precond (s)) :
    runLengthEncode_postcond (s) (runLengthEncode (s) h_precond) h_precond := by
  sorry
-- </vc-theorems>