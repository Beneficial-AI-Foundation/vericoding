-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_xor_parity (n m : Nat) (arr queries : List Nat) : List String :=
  sorry

def popCount (n : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_xor_parity_output_format {n m : Nat} {arr queries : List Nat}
    (h1 : arr.length > 0) (h2 : queries.length > 0)
    (h3 : arr.length = n) (h4 : queries.length = m) :
    let result := solve_xor_parity n m arr queries
    result.length = queries.length ∧
    ∀ r ∈ result,
      ∃ evens odds : Nat,
        r = toString evens ++ " " ++ toString odds ∧
        evens + odds = arr.length :=
sorry

theorem solve_xor_parity_idempotent {n : Nat} {arr : List Nat} {query : Nat}
    (h : arr.length > 0) (h2 : arr.length = n) :
    solve_xor_parity n 1 arr [query] = solve_xor_parity n 1 arr [query] :=
sorry

theorem solve_xor_parity_singleton {x query : Nat} :
    let result := solve_xor_parity 1 1 [x] [query]
    let r := result[0]!
    let evens := (r.splitOn " ")[0]!.toNat!
    let odds := (r.splitOn " ")[1]!.toNat!
    evens + odds = 1 ∧
    (if (popCount (x.xor query)) % 2 = 0
     then evens = 1 ∧ odds = 0
     else evens = 0 ∧ odds = 1) :=
sorry
-- </vc-theorems>