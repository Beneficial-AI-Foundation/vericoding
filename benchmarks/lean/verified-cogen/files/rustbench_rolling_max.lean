-- <vc-preamble>
-- Recursive function to compute maximum of a sequence
def seq_max (a : List Int) : Int :=
  match a with
  | [] => -2147483648  -- i32::MIN equivalent
  | [x] => x
  | x :: xs => max x (seq_max xs)

@[reducible, simp]
def rollingMax_precond (numbers : Array Int) : Prop := True
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

def main : IO Unit := pure ()