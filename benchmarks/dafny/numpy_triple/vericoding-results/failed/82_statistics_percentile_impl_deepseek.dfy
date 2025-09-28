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
function Sort(arr: seq<real>): seq<real>
  ensures |Sort(arr)| == |arr|
  ensures forall i, j :: 0 <= i < j < |Sort(arr)| ==> Sort(arr)[i] <= Sort(arr)[j]
{
  if |arr| <= 1 then arr
  else
    var pivot := arr[0];
    var smaller := [x | x in arr[1..], x <= pivot];
    var larger := [x | x in arr[1..], x > pivot];
    Sort(smaller) + [pivot] + Sort(larger)
}

// Helper lemma to establish properties of sorted arrays
lemma SortedArrayPercentileProperties(sortedArr: seq<real>, q: real, result: real)
  requires |sortedArr| > 0
  requires 0.0 <= q <= 100.0
  requires forall i, j :: 0 <= i < j < |sortedArr| ==> sortedArr[i] <= sortedArr[j]
  ensures MinValue(sortedArr) <= result <= MaxValue(sortedArr)
  ensures CountLessOrEqual(sortedArr, result) as real >= (q / 100.0) * |sortedArr| as real
  ensures CountGreaterOrEqual(sortedArr, result) as real >= ((100.0 - q) / 100.0) * |sortedArr| as real
  ensures q == 0.0 ==> result == MinValue(sortedArr)
  ensures q == 100.0 ==> result == MaxValue(sortedArr)
  ensures exists i :: 0 <= i < |sortedArr| && sortedArr[i] <= result
  ensures exists i :: 0 <= i < |sortedArr| && sortedArr[i] >= result
{
  var index := (|sortedArr| as real * q / 100.0).Floor as int;
  if index < 0 { index := 0; }
  if index >= |sortedArr| { index := |sortedArr| - 1; }
  
  // Prove min/max bounds
  var min_val := MinValue(sortedArr);
  var max_val := MaxValue(sortedArr);
  assert forall i :: 0 <= i < |sortedArr| ==> min_val <= sortedArr[i] <= max_val;
  assert sortedArr[0] == min_val;
  assert sortedArr[|sortedArr|-1] == max_val;
  
  // Special cases
  if q == 0.0 {
    assert result == sortedArr[0];
    assert result == min_val;
  } else if q == 100.0 {
    assert result == sortedArr[|sortedArr|-1];
    assert result == max_val;
  }
  
  // Prove percentile properties
  assert index == if q == 0.0 then 0 else if q == 100.0 then |sortedArr| - 1 else index;
  assert CountLessOrEqual(sortedArr, result) >= index + 1;
  assert CountGreaterOrEqual(sortedArr, result) >= |sortedArr| - index;
  
  // Mathematical properties
  assert (index + 1) as real >= (q / 100.0) * |sortedArr| as real;
  assert (|sortedArr| - index) as real >= ((100.0 - q) / 100.0) * |sortedArr| as real;
}

// Helper function to find the percentile index in a sorted array
function FindPercentileIndex(sortedArr: seq<real>, q: real): int
  requires |sortedArr| > 0
  requires 0.0 <= q <= 100.0
  requires forall i, j :: 0 <= i < j < |sortedArr| ==> sortedArr[i] <= sortedArr[j]
  ensures 0 <= FindPercentileIndex(sortedArr, q) < |sortedArr|
{
  var indexReal := (|sortedArr| as real * q / 100.0);
  var index := indexReal.Floor as int;
  if index < 0 then 0
  else if index >= |sortedArr| then |sortedArr| - 1
  else index
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
  /* code modified by LLM (iteration 5): Fixed list comprehension syntax */
  // Create a sorted copy of the array
  var sortedArr := Sort(arr);
  
  // Find the appropriate index for the percentile
  var index := FindPercentileIndex(sortedArr, q);
  result := sortedArr[index];
  
  // Verify the properties using the helper lemma
  SortedArrayPercentileProperties(sortedArr, q, result);
}
// </vc-code>
