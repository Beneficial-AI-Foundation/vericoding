-- <vc-preamble>
def TimeMap.set (tm : TimeMap) (key : String) (value : String) (timestamp : Nat) : TimeMap :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def TimeMap.get (tm : TimeMap) (key : String) (timestamp : Nat) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem set_then_get_returns_same_value 
  (key : String) (value : String) (timestamp : Nat) :
  ∀ tm : TimeMap,
  TimeMap.get (TimeMap.set tm key value timestamp) key timestamp = value :=
sorry

theorem multiple_values_preserved_order
  (key : String) (value1 value2 : String) (ts1 ts2 : Nat) :
  ts1 ≠ ts2 →
  let first_ts := min ts1 ts2
  let second_ts := max ts1 ts2
  let first_val := if ts1 < ts2 then value1 else value2
  let second_val := if ts1 < ts2 then value2 else value1
  ∀ tm : TimeMap,
  let tm' := TimeMap.set tm key first_val first_ts
  let tm'' := TimeMap.set tm' key second_val second_ts
  (TimeMap.get tm'' key first_ts = first_val) ∧
  (TimeMap.get tm'' key second_ts = second_val) :=
sorry

theorem timestamp_boundaries
  (key : String) (value : String) (timestamp query_time : Nat) :
  ∀ tm : TimeMap,
  let tm' := TimeMap.set tm key value timestamp
  (query_time < timestamp → 
    TimeMap.get tm' key query_time = "" ∨ 
    TimeMap.get tm' key query_time = value) ∧
  (query_time ≥ timestamp →
    TimeMap.get tm' key query_time = value) :=
sorry

theorem nonexistent_key
  (key : String) (timestamp : Nat) :
  ∀ tm : TimeMap,
  TimeMap.get tm key timestamp = "" :=
sorry
-- </vc-theorems>