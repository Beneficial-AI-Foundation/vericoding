-- <vc-preamble>
def splitOnSpace (s : String) : List String :=
  s.split (fun c => c = ' ')
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def fizz_buzz_cuckoo_clock (time : String) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem output_is_nonempty (time : String) :
  time.length = 5 → (fizz_buzz_cuckoo_clock time).length > 0 :=
sorry

theorem half_hour_single_cuckoo (hour : Nat) (h : hour ≤ 23) :
  let time := (if hour < 10 then "0" else "") ++ toString hour ++ ":30"
  fizz_buzz_cuckoo_clock time = "Cuckoo" :=
sorry
-- </vc-theorems>