// <vc-preamble>
// Helper function to count elements less than or equal to a value
ghost function CountLessOrEqual(arr: seq<real>, value: real): nat
{
  |set i | 0 <= i < |arr| && arr[i] <= value|
}

// Helper function to count elements greater than or equal to a value  
ghost function CountGreaterOrEqual(arr: seq<real>, value: real): nat
{
  |set i | 0 <= i < |arr| && arr[i] >= value|
}

// Helper function to get minimum value in array
ghost function MinValue(arr: seq<real>): real
  requires |arr| > 0
{
  if |arr| == 1 then arr[0]
  else if arr[0] <= MinValue(arr[1..]) then arr[0]
  else MinValue(arr[1..])
}

// Helper function to get maximum value in array
ghost function MaxValue(arr: seq<real>): real
  requires |arr| > 0
{
  if |arr| == 1 then arr[0]
  else if arr[0] >= MaxValue(arr[1..]) then arr[0]
  else MaxValue(arr[1..])
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): removed invalid {:inductive} annotation to fix compilation error and defined helper functions for sorting */

function Insert(sorted: seq<real>, val: real): seq<real>
  requires IsSorted(sorted)
  ensures IsSorted(Insert(sorted, val))
  ensures multiset(sorted) + multiset([val]) == multiset(Insert(sorted, val))
  decreases |sorted|
{
  if sorted == [] then [val]
  else if val <= sorted[0] then [val] + sorted
  else [sorted[0]] + Insert(sorted[1..], val)
}

function SortedArr(arr: seq<real>): seq<real>
  decreases |arr|
  ensures IsSorted(SortedArr(arr))
  ensures multiset(arr) == multiset(SortedArr(arr))
{
  if |arr| == 0 then []
  else Insert(SortedArr(arr[1..]), arr[0])
}

predicate IsSorted(s: seq<real>) decreases |s|
{
  if |s| <= 1 then true
  else s[0] <= s[1] && IsSorted(s[1..])
}
// </vc-helpers>

// <vc-spec>
method Percentile(arr: seq<real>, q: real) returns (result: real)
  // Input validation: array must be non-empty and q must be valid percentile
  requires |arr| > 0
  requires 0.0 <= q <= 100.0
  
  // The result must be bounded by the array's min and max values
  ensures MinValue(arr) <= result <= MaxValue(arr)
  
  // Percentile property: at least q% of values are <= result
  ensures CountLessOrEqual(arr, result) as real >= (q / 100.0) * |arr| as real
  
  // Percentile property: at least (100-q)% of values are >= result  
  ensures CountGreaterOrEqual(arr, result) as real >= ((100.0 - q) / 100.0) * |arr| as real
  
  // Special case: 0th percentile is the minimum
  ensures q == 0.0 ==> result == MinValue(arr)
  
  // Special case: 100th percentile is the maximum
  ensures q == 100.0 ==> result == MaxValue(arr)
  
  // For any percentile, there exists at least one element <= result and >= result
  ensures exists i :: 0 <= i < |arr| && arr[i] <= result
  ensures exists i :: 0 <= i < |arr| && arr[i] >= result
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): kept the percentile implementation using sorted array for precise calculation */
{
  var sorted := SortedArr(arr);
  var n := |arr|;
  var factor : real := (q / 100.0) * ((n - 1) as real);
  var index := factor.Floor as int;
  if index < 0 { index := 0; }
  if index >= n { index := n - 1; }
  result := sorted[index];
}
// </vc-code>
