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

def String.splitColumns (s : String) : List String := sorry

def List.sum (l : List Nat) : Nat := l.foldl (· + ·) 0

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: guarded