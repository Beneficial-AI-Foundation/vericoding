-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_borrowed_books (n : Nat) (books : List Nat) (k : Nat) (positions : List Nat) : List Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem find_borrowed_books_middle_and_end 
  (books : List Nat := [26, 1, 42, 15, 3])
  (n : Nat := 5)
  (k : Nat := 2) 
  (positions : List Nat := [3, 4]) :
  find_borrowed_books n books k positions = [42, 3] :=
sorry

theorem find_borrowed_books_start
  (books : List Nat := [1, 2, 3])
  (n : Nat := 3)
  (k : Nat := 2)
  (positions : List Nat := [2, 1]) :
  find_borrowed_books n books k positions = [2, 1] :=
sorry

theorem find_borrowed_books_single
  (books : List Nat := [10, 20, 30]) 
  (n : Nat := 3)
  (k : Nat := 1)
  (positions : List Nat := [2]) :
  find_borrowed_books n books k positions = [20] :=
sorry

theorem find_borrowed_books_length
  (n : Nat)
  (books : List Nat)
  (k : Nat)
  (positions : List Nat)
  (h1 : k = positions.length)
  (h2 : k ≤ n)
  (h3 : n = books.length) :
  (find_borrowed_books n books k positions).length = k :=
sorry
-- </vc-theorems>