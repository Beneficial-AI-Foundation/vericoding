-- <vc-preamble>
def binary_units := ["KiB", "MiB", "GiB", "TiB"]

def metric_units := ["kB", "MB", "GB", "TB"]

def isValidIndex (i : Nat) : Prop :=
  i < 4
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def memorysize_conversion (s : String) : String :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem binary_units_length : binary_units.length = 4 :=
sorry

theorem metric_units_length : metric_units.length = 4 :=
sorry

theorem binary_to_metric_unit_preservation {value : Float} {unit_idx : Nat}
  (h1 : 0.000001 ≤ value) (h2 : value ≤ 1000000)
  (h3 : isValidIndex unit_idx) :
  let input := s!"{value} {binary_units[unit_idx]}"
  let result := memorysize_conversion input
  result.endsWith metric_units[unit_idx] :=
sorry

theorem metric_to_binary_unit_preservation {value : Float} {unit_idx : Nat}
  (h1 : 0.000001 ≤ value) (h2 : value ≤ 1000000)
  (h3 : isValidIndex unit_idx) :
  let input := s!"{value} {metric_units[unit_idx]}"
  let result := memorysize_conversion input
  result.endsWith binary_units[unit_idx] :=
sorry
-- </vc-theorems>