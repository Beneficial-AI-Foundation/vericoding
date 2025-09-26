import Mathlib
-- <vc-preamble>
def ValidWeather (weather : String) : Bool :=
  weather == "Sunny" || weather == "Cloudy" || weather == "Rainy"

def TrimNewline (input : String) : String :=
  if input.length > 0 && input.data[input.length - 1]! == '\n' then 
    String.mk (input.data.extract 0 (input.length - 1))
  else 
    input

def NextWeather (weather : String) : String :=
  if weather == "Sunny" then "Cloudy"
  else if weather == "Cloudy" then "Rainy"
  else "Sunny"

@[reducible, simp]
def solve_precond (input : String) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER: no additional helpers required for this verification task.
-- </vc-helpers>

-- <vc-definitions>
def solve (input : String) (_ : solve_precond input) : String :=
    let trimmed := TrimNewline input
  if ValidWeather trimmed then
    NextWeather trimmed ++ "\n"
  else
    ""
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (input : String) (result : String) (_ : solve_precond input) : Prop :=
  let trimmed := TrimNewline input
  if ValidWeather trimmed then 
    result = NextWeather trimmed ++ "\n"
  else 
    result = ""

theorem solve_spec_satisfied (input : String) (h_precond : solve_precond input) :
    solve_postcond input (solve input h_precond) h_precond := by
    cases h : ValidWeather (TrimNewline input) <;> simp [solve_postcond, solve, h]
-- </vc-theorems>
