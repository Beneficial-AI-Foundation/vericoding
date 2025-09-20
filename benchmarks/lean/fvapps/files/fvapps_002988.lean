-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def seven_ate9 (s : String) : String :=
sorry

def countSubstr (s : String) (sub : String) : Nat :=
sorry

def containsSubstr (s : String) (sub : String) : Bool :=
sorry
-- </vc-definitions>

-- <vc-theorems>
def iterativeReplace (s : String) (n : Nat) : String :=
  match n with
  | 0 => s
  | n + 1 =>
    if containsSubstr s "797"
    then iterativeReplace (s.replace "797" "77") n
    else s

theorem output_is_string {s : String} :
  s.all (fun c => c.isDigit) →
  (seven_ate9 s).all (fun c => c.isDigit) :=
sorry

theorem output_length_correct {s : String} :
  s.all (fun c => c.isDigit) →
  (seven_ate9 s).length = s.length - (countSubstr s "797") :=
sorry

theorem no_797_in_result {s : String} :
  s.all (fun c => c.isDigit) →
  ¬(containsSubstr (seven_ate9 s) "797") :=
sorry

theorem only_797_modified {s : String} :
  s.all (fun c => c.isDigit) →
  seven_ate9 s = iterativeReplace s s.length :=
sorry
-- </vc-theorems>