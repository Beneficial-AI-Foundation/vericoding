-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_book_pages (n m : Nat) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_book_pages_nonnegative (n m : Nat) 
    (h1 : n > 0) (h2 : m > 0) :
  solve_book_pages n m ≥ 0 :=
sorry

theorem solve_book_pages_equals_sum (n m : Nat)
    (h1 : n > 0) (h2 : m > 0) :
  solve_book_pages n m = 
    (List.range (n / m)).foldl (fun acc i => acc + ((i + 1) * m % 10)) 0 :=
sorry

theorem divisibility_property (n m : Nat)
    (h1 : n > 0) (h2 : m > 0) :
  solve_book_pages n m = solve_book_pages (n - n % m) m :=
sorry
-- </vc-theorems>