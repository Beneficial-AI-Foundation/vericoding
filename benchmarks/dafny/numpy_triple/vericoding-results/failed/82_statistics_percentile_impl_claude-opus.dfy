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
function SortedSeq(arr: seq<real>): seq<real>
  ensures |SortedSeq(arr)| == |arr|
  ensures multiset(SortedSeq(arr)) == multiset(arr)
  ensures forall i, j :: 0 <= i < j < |SortedSeq(arr)| ==> SortedSeq(arr)[i] <= SortedSeq(arr)[j]
  ensures forall i :: 0 <= i < |arr| ==> exists j :: 0 <= j < |SortedSeq(arr)| && arr[i] == SortedSeq(arr)[j]
  ensures |arr| > 0 ==> SortedSeq(arr)[0] == MinValue(arr)
  ensures |arr| > 0 ==> SortedSeq(arr)[|arr|-1] == MaxValue(arr)
{
  if |arr| <= 1 then arr
  else
    var pivot := arr[0];
    var less := seq(|arr|-1, i requires 0 <= i < |arr|-1 => arr[i+1])[i | i in [0..|arr|-1] && arr[i+1] < pivot];
    var equal := seq(|arr|, i requires 0 <= i < |arr| => arr[i])[i | i in [0..|arr|] && arr[i] == pivot];
    var greater := seq(|arr|-1, i requires 0 <= i < |arr|-1 => arr[i+1])[i | i in [0..|arr|-1] && arr[i+1] > pivot];
    SortedSeq(less) + equal + SortedSeq(greater)
}

lemma SortedSeqProperties(arr: seq<real>, value: real)
  requires |arr| > 0
  ensures CountLessOrEqual(arr, value) == |set i | 0 <= i < |SortedSeq(arr)| && SortedSeq(arr)[i] <= value|
  ensures CountGreaterOrEqual(arr, value) == |set i | 0 <= i < |SortedSeq(arr)| && SortedSeq(arr)[i] >= value|
{}

function PercentileIndex(n: nat, q: real): nat
  requires n > 0
  requires 0.0 <= q <= 100.0
  ensures 0 <= PercentileIndex(n, q) < n
{
  var idx := ((q / 100.0) * (n - 1) as real) as int;
  if idx < 0 then 0
  else if idx >= n then n - 1
  else idx
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
{
  var sorted := SortedSeq(arr);
  var idx := PercentileIndex(|arr|, q);
  result := sorted[idx];
  SortedSeqProperties(arr, result);
}
// </vc-code>
