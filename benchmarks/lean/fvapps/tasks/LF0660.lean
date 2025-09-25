-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_books (books : List String) (queries : List String) : List String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem count_books_result_length {books queries : List String} :
  List.length (count_books books queries) = List.length queries :=
  sorry

theorem count_books_nonnegative {books queries : List String} :
  ∀ result ∈ count_books books queries,
    ∀ n : Nat, (result.splitOn " ").head! = toString n → n ≥ 0 :=
  sorry 

theorem count_books_correct_count {books queries : List String} :
  ∀ (i : Nat), i < queries.length →
    let result := List.get! (count_books books queries) i
    let count := ((result.splitOn " ").head!).toNat!
    let query := List.get! queries i
    count = List.length (List.filter (fun book => book.startsWith query) books) :=
  sorry
-- </vc-theorems>