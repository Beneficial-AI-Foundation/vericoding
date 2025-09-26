-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isLinear (xs : List Int) : Bool := sorry

theorem linear_sequence_gives_linear_function
  {seq : List Int} (h : seq.length = 5) (hlin : isLinear seq) :
  ∃ f : Int → Int, get_function seq = Sum.inl f ∧
  ∀ x : Int, f x = (seq[1]! - seq[0]!) * x + seq[0]! :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem nonlinear_sequence_gives_error
  {seq : List Int} (h : seq.length = 5) (hnlin : ¬isLinear seq) :
  get_function seq = Sum.inr "Non-linear sequence" :=
sorry

theorem linear_function_matches_input_points
  {seq : List Int} (h : seq.length = 5) (hlin : isLinear seq) :
  match get_function seq with
  | Sum.inl f => ∀ i : Fin 5, f i.val = seq[i]!
  | Sum.inr _ => False :=
sorry

/-
info: 5
-/
-- #guard_msgs in
-- #eval f1 5

/-
info: 30
-/
-- #guard_msgs in
-- #eval f2 10
-- </vc-theorems>