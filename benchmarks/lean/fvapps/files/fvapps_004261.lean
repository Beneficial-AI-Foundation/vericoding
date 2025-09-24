-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def Day := String
def am_I_afraid (day : Day) (num : Int) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem am_I_afraid_type_is_bool (day : Day) (num : Int) :
  ∀ result, result = am_I_afraid day num → result = true ∨ result = false :=
  sorry

theorem am_I_afraid_monday (num : Int) :
  am_I_afraid "Monday" num = (num = 12) :=
  sorry

theorem am_I_afraid_tuesday (num : Int) :
  am_I_afraid "Tuesday" num = (num > 95) :=
  sorry

theorem am_I_afraid_wednesday (num : Int) :
  am_I_afraid "Wednesday" num = (num = 34) :=
  sorry

theorem am_I_afraid_thursday (num : Int) :
  am_I_afraid "Thursday" num = (num = 0) :=
  sorry

theorem am_I_afraid_friday (num : Int) :
  am_I_afraid "Friday" num = (num % 2 = 0) :=
  sorry

theorem am_I_afraid_saturday (num : Int) :
  am_I_afraid "Saturday" num = (num = 56) :=
  sorry

theorem am_I_afraid_sunday (num : Int) :
  am_I_afraid "Sunday" num = (num = 666 ∨ num = -666) :=
  sorry

theorem am_I_afraid_monday_boundary :
  am_I_afraid "Monday" 12 = true ∧
  am_I_afraid "Monday" 11 = false :=
  sorry

theorem am_I_afraid_tuesday_boundary :
  am_I_afraid "Tuesday" 96 = true ∧
  am_I_afraid "Tuesday" 95 = false :=
  sorry

theorem am_I_afraid_friday_boundary :
  am_I_afraid "Friday" 0 = true ∧
  am_I_afraid "Friday" 1 = false :=
  sorry
-- </vc-theorems>