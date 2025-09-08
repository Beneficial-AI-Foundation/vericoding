/-
# Task
 A common way for prisoners to communicate secret messages with each other is to encrypt them. One such encryption algorithm goes as follows.

 You take the message and place it inside an `nx6` matrix (adjust the number of rows depending on the message length) going from top left to bottom right (one row at a time) while replacing spaces with dots (.) and adding dots at the end of the last row (if necessary) to complete the matrix.

 Once the message is in the matrix you read again from top left to bottom right but this time going one column at a time and treating each column as one word.

# Example

 The following message `"Attack at noon or we are done for"` is placed in a `6 * 6` matrix :
```
Attack
.at.no
on.or.
we.are
.done.
for...```
Reading it one column at a time we get:

 `A.ow.f tanedo tt..or a.oan. cnrre. ko.e..`

# Input/Output

 - `[input]` string `msg`

  a regular english sentance representing the original message

 - `[output]` a string

  encrypted message
-/

def String.splitColumns (s : String) : List String := sorry

def List.sum (l : List Nat) : Nat := l.foldl (· + ·) 0

-- <vc-helpers>
-- </vc-helpers>

def six_column_encryption (msg : String) : String := sorry

theorem encryption_correct_columns (msg : String) : 
  (six_column_encryption msg).splitColumns.length = 6
  := sorry

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

-- Apps difficulty: introductory
-- Assurance level: guarded