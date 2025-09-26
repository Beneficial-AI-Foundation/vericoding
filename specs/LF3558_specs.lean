-- <vc-preamble>
def String.splitColumns (s : String) : List String := sorry

def List.sum (l : List Nat) : Nat := l.foldl (· + ·) 0
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def six_column_encryption (msg : String) : String := sorry

theorem encryption_correct_columns (msg : String) : 
  (six_column_encryption msg).splitColumns.length = 6
  := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem encryption_length_divisible_by_six (msg : String) :
  let columns := (six_column_encryption msg).splitColumns
  let total_chars := (columns.map String.length).sum
  total_chars % 6 = 0
  := sorry

theorem encryption_preserves_length (msg : String) :
  let result := six_column_encryption msg
  let result_chars := result.splitColumns.foldl (· ++ ·) ""
  let padded_len := msg.length + ((6 - msg.length % 6) % 6)
  result_chars.length = padded_len
  := sorry 

theorem encryption_balanced_columns (msg : String) :
  let result := six_column_encryption msg
  let lengths := result.splitColumns.map String.length
  match lengths.maximum?, lengths.minimum? with
  | some max, some min => max - min ≤ 1
  | _, _ => True
  := sorry
-- </vc-theorems>