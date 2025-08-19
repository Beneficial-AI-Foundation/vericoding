import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-!
{
  "name": "numpy.datetime_data",
  "category": "Datetime metadata",
  "description": "Get information about the step size of a date or time type",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.datetime_data.html",
  "doc": "datetime_data(dtype, /)\n\nGet information about the step size of a date or time type.\n\nThe returned tuple can be passed as the second argument of \`numpy.datetime64\` and \`numpy.timedelta64\`.\n\nParameters\n----------\ndtype : dtype\n    The dtype object, which must be a \`datetime64\` or \`timedelta64\` type.\n\nReturns\n-------\nunit : str\n    The :ref:\`datetime unit <arrays.dtypes.dateunits>\` on which this dtype is based.\ncount : int\n    The number of base units in a step.\n\nExamples\n--------\n>>> import numpy as np\n>>> dt_25s = np.dtype('timedelta64[25s]')\n>>> np.datetime_data(dt_25s)\n('s', 25)\n>>> np.array(10, dt_25s).astype('timedelta64[s]')\narray(250, dtype='timedelta64[s]')\n\nThe result can be used to construct a datetime that uses the same units as a timedelta\n\n>>> np.datetime64('2010', np.datetime_data(dt_25s))\nnp.datetime64('2010-01-01T00:00:00','25s')",
  "code": "# C implementation for performance\n# Get information about the step size of a date or time type\n#\n# This function is implemented in C as part of NumPy's core multiarray module.\n# The C implementation provides:\n# - Optimized memory access patterns\n# - Efficient array manipulation\n# - Low-level control over data layout\n# - Integration with NumPy's array object internals\n#\n# Source: C implementation in numpy/_core/src/multiarray/datetime.c"
}
-/

/-- Datetime unit enumeration representing the time scales used in datetime operations -/
inductive DatetimeUnit
  /-- Years -/
  | Y    
  /-- Months -/
  | M    
  /-- Weeks -/
  | W    
  /-- Days -/
  | D    
  /-- Hours -/
  | h    
  /-- Minutes -/
  | m    
  /-- Seconds -/
  | s    
  /-- Milliseconds -/
  | ms   
  /-- Microseconds -/
  | us   
  /-- Nanoseconds -/
  | ns   

/-- Structure containing datetime type information including unit and count -/
structure DatetimeTypeInfo where
  /-- The time unit (seconds, minutes, hours, etc.) -/
  unit : DatetimeUnit
  /-- The count of base units in a step (e.g., 25 for "25 seconds") -/
  count : Nat

/-- Datetime dtype representing either datetime64 or timedelta64 types -/
inductive DatetimeDtype
  /-- A datetime64 type with specified unit and count -/
  | datetime64 : DatetimeTypeInfo → DatetimeDtype
  /-- A timedelta64 type with specified unit and count -/
  | timedelta64 : DatetimeTypeInfo → DatetimeDtype

/-- Get information about the step size of a date or time type.
    
    Returns a tuple containing the datetime unit and count for the given dtype.
    This information can be used to construct datetime64 and timedelta64 objects.
    
    For example, 'timedelta64[25s]' would return ('s', 25).
-/
def datetime_data (dtype : DatetimeDtype) : Id (DatetimeUnit × Nat) :=
  match dtype with
  | DatetimeDtype.datetime64 info => return (info.unit, info.count)
  | DatetimeDtype.timedelta64 info => return (info.unit, info.count)

-- LLM HELPER
lemma count_pos_from_info (info : DatetimeTypeInfo) (h : info.count > 0) : info.count > 0 := h

-- LLM HELPER
lemma datetime_data_eq_for_datetime64 (info : DatetimeTypeInfo) :
    datetime_data (DatetimeDtype.datetime64 info) = return (info.unit, info.count) := by
  simp [datetime_data]

-- LLM HELPER
lemma datetime_data_eq_for_timedelta64 (info : DatetimeTypeInfo) :
    datetime_data (DatetimeDtype.timedelta64 info) = return (info.unit, info.count) := by
  simp [datetime_data]

/-- Specification: datetime_data extracts the unit and count from a datetime dtype.
    
    Precondition: The dtype must be a valid datetime64 or timedelta64 type.
    Postcondition: The returned tuple contains the unit and count that define the dtype.
    
    For datetime64[N unit], returns (unit, N).
    For timedelta64[N unit], returns (unit, N).
    
    This ensures that the returned information can be used to reconstruct
    the original dtype or create compatible datetime objects.
-/
theorem datetime_data_spec (dtype : DatetimeDtype) :
    ⦃⌜True⌝⦄
    datetime_data dtype
    ⦃⇓result => ⌜match dtype with
       | DatetimeDtype.datetime64 info => result = (info.unit, info.count) ∧ result.2 > 0
       | DatetimeDtype.timedelta64 info => result = (info.unit, info.count) ∧ result.2 > 0⌝⦄ := by
  cases dtype with
  | datetime64 info =>
    rw [datetime_data_eq_for_datetime64]
    apply hoare_return
    simp
    exact ⟨rfl, by assumption⟩
  | timedelta64 info =>
    rw [datetime_data_eq_for_timedelta64]
    apply hoare_return
    simp
    exact ⟨rfl, by assumption⟩