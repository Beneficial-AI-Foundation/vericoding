-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def answer (question : String) (info_list : List String) : Option String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem answer_none_on_empty_list (q : String) :
  answer q [] = none := by sorry

theorem result_in_info_list (q : String) (info_list : List String) :
  let r := answer q info_list
  match r with
  | none => True
  | some result => result ∈ info_list
  := by sorry

theorem result_shares_words (q : String) (info_list : List String) :
  let r := answer q info_list
  match r with
  | none => True
  | some result =>
    ∃ word ∈ (String.splitOn q " ").map String.toLower,
    word ∈ String.splitOn result.toLower " "
  := by sorry

theorem result_has_max_overlap (q : String) (info_list : List String) :
  let r := answer q info_list
  match r with
  | none => True
  | some result =>
    let qwords := String.splitOn q.toLower " "
    let score (s : String) := (qwords.filter (λ w => w ∈ String.splitOn s.toLower " ")).length
    ∀ info ∈ info_list, score result ≥ score info
  := by sorry

theorem single_answer_behavior (q : String) (info : String) :
  let qwords := String.splitOn q.toLower " "
  let iwords := String.splitOn info.toLower " "
  let shares_words := ∃ w ∈ qwords, w ∈ iwords
  answer q [info] = if shares_words then some info else none
  := by sorry
-- </vc-theorems>