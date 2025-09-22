-- <vc-preamble>
def isVerdict (s : String) : Bool :=
  s = "POSSIBLE" || s = "IMPOSSIBLE"

def isVerdictWithNumber (s : String) : Bool :=
  let parts := s.splitOn " "
  match parts with
  | [verdict, num] => isVerdict verdict && (num.toInt?.isSome)
  | _ => false
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_cake_festival (families : List (Nat × Nat × Nat × Nat)) : List String := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem cake_festival_output_format (families : List (Nat × Nat × Nat × Nat)) :
  let results := solve_cake_festival families;

  results.length > 0

  ∧ (∀ i : Fin (results.length - 1), isVerdictWithNumber results[i]!)

  ∧ isVerdict results[results.length - 1]! :=
sorry

theorem cake_festival_valid_diffs (families : List (Nat × Nat × Nat × Nat)) :
  let results := solve_cake_festival families;
  results.length = families.length + 1
  ∧ ∀ i : Fin families.length,
    let (slices, _, _, _) := families[i];
    let parts := (results[i]!).splitOn " ";
    match parts with
    | ["POSSIBLE", n] => (n.toInt?.get! ≥ 0)
    | ["IMPOSSIBLE", n] => (n.toInt?.get! > 0)
    | _ => False :=
sorry

theorem cake_festival_final_verdict (families : List (Nat × Nat × Nat × Nat)) :
  let results := solve_cake_festival families;
  let extra := results.take (results.length - 1) |>.foldl (λ acc res =>
    let parts := res.splitOn " "
    match parts with
    | ["POSSIBLE", n] => acc + n.toInt?.getD 0
    | _ => acc) 0;
  let less := results.take (results.length - 1) |>.foldl (λ acc res =>
    let parts := res.splitOn " "
    match parts with
    | ["IMPOSSIBLE", n] => acc + n.toInt?.getD 0
    | _ => acc) 0;
  results[results.length - 1]! = "POSSIBLE" ↔ extra ≥ less :=
sorry

theorem single_member_family
  (slices smallest luck : Nat)
  (h1 : slices > 0) (h2 : smallest > 0) (h3 : luck > 0) :
  let results := solve_cake_festival [(slices, 1, smallest, luck)];
  results.length = 2
  ∧ if smallest ≤ slices then
      results[0]! = s!"POSSIBLE {slices - smallest}"
    else
      results[0]! = s!"IMPOSSIBLE {smallest - slices}" :=
sorry
-- </vc-theorems>