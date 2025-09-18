// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): simplified sorting helper function */
function insert_sorted(x: int, sorted: seq<int>): seq<int>
  requires forall i :: 0 <= i < |sorted| - 1 ==> sorted[i] <= sorted[i + 1]
  ensures forall i :: 0 <= i < |insert_sorted(x, sorted)| - 1 ==> insert_sorted(x, sorted)[i] <= insert_sorted(x, sorted)[i + 1]
  ensures x in insert_sorted(x, sorted)
  ensures forall y :: y in sorted ==> y in insert_sorted(x, sorted)
  ensures forall y :: y in insert_sorted(x, sorted) ==> y == x || y in sorted
{
  if |sorted| == 0 then [x]
  else if x <= sorted[0] then [x] + sorted
  else [sorted[0]] + insert_sorted(x, sorted[1..])
}
// </vc-helpers>

// <vc-spec>
method UniqueSorted(arr: array<int>) returns (result: array<int>)
    ensures result.Length <= arr.Length
    ensures forall i :: 0 <= i < result.Length - 1 ==> result[i] <= result[i + 1]
    ensures forall x :: x in arr[..] <==> x in result[..]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): corrected invariants and ensured proper sorted order maintenance */
  var temp := new int[arr.Length];
  var i := 0;
  while i < arr.Length
    invariant 0 <= i <= arr.Length
    invariant forall k :: 0 <= k < i ==> temp[k] == arr[k]
  {
    temp[i] := arr[i];
    i := i + 1;
  }
  
  // Sort the array using insertion sort
  if temp.Length > 0 {
    i := 1;
    while i < temp.Length
      invariant 1 <= i <= temp.Length
      invariant forall j :: 0 <= j < i - 1 ==> temp[j] <= temp[j + 1]
      invariant forall x :: x in temp[..] <==> x in arr[..]
    {
      var key := temp[i];
      var j := i - 1;
      while j >= 0 && temp[j] > key
        invariant -1 <= j < i
        invariant forall k :: j + 2 <= k <= i ==> temp[k] > key
        invariant temp[j + 1] == key || (j + 1 < i && temp[j + 1] > key)
        invariant forall x :: x in temp[..] <==> x in arr[..]
      {
        temp[j + 1] := temp[j];
        j := j - 1;
      }
      temp[j + 1] := key;
      i := i + 1;
    }
  }
  
  // Count unique elements first
  var uniqueCount := 0;
  i := 0;
  while i < temp.Length
    invariant 0 <= i <= temp.Length
    invariant 0 <= uniqueCount <= i
  {
    if i == 0 || temp[i] != temp[i - 1] {
      uniqueCount := uniqueCount + 1;
    }
    i := i + 1;
  }
  
  // Create result array and fill with unique elements
  result := new int[uniqueCount];
  if uniqueCount > 0 {
    var resultIndex := 0;
    i := 0;
    while i < temp.Length && resultIndex < result.Length
      invariant 0 <= i <= temp.Length
      invariant 0 <= resultIndex <= result.Length
      invariant resultIndex <= uniqueCount
      invariant resultIndex > 0 ==> (forall k :: 0 <= k < resultIndex - 1 ==> result[k] <= result[k + 1])
      invariant forall x :: x in result[..resultIndex] ==> x in arr[..]
      invariant forall k :: 0 <= k < resultIndex ==> (exists j :: 0 <= j < i && temp[j] == result[k])
    {
      if i == 0 || temp[i] != temp[i - 1] {
        if resultIndex > 0 {
          assert temp[i - 1] <= temp[i];
          assert result[resultIndex - 1] <= temp[i];
        }
        result[resultIndex] := temp[i];
        resultIndex := resultIndex + 1;
      }
      i := i + 1;
    }
  }
}
// </vc-code>
