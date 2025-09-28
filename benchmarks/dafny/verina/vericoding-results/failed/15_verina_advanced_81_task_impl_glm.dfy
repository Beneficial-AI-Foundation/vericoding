// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method UniqueSorted(arr: array<int>) returns (result: array<int>)
    ensures result.Length <= arr.Length
    ensures forall i :: 0 <= i < result.Length - 1 ==> result[i] <= result[i + 1]
    ensures forall x :: x in arr[..] <==> x in result[..]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): removed CountDistinct call and added invariants */
  if arr.Length == 0 {
    result := new int[0];
    return;
  }
  
  // Count distinct elements
  var distinctCount := 0;
  var i := 0;
  while i < arr.Length
    invariant 0 <= i <= arr.Length
    invariant 0 <= distinctCount <= i
  {
    var j := 0;
    var found := false;
    while j < i
      invariant 0 <= j <= i
    {
      if arr[j] == arr[i] {
        found := true;
      }
      j := j + 1;
    }
    
    if !found {
      distinctCount := distinctCount + 1;
    }
    i := i + 1;
  }
  
  result := new int[distinctCount];
  var resultIndex := 0;
  
  // Fill result with distinct elements
  i := 0;
  while i < arr.Length
    invariant 0 <= i <= arr.Length
    invariant 0 <= resultIndex <= distinctCount
    invariant forall k :: 0 <= k < resultIndex ==> result[k] in arr[0..i]
    invariant forall k :: 0 <= k < resultIndex ==> (forall m :: 0 <= m < k ==> result[m] != result[k])
    invariant forall x :: x in arr[0..i] && (forall m :: 0 <= m < i ==> arr[m] != x) ==> x in result[0..resultIndex]
  {
    var j := 0;
    var found := false;
    while j < i
      invariant 0 <= j <= i
      invariant found ==> (exists m :: 0 <= m < j && arr[m] == arr[i])
      invariant !found ==> (forall m :: 0 <= m < j ==> arr[m] != arr[i])
    {
      if arr[j] == arr[i] {
        found := true;
      }
      j := j + 1;
    }
    
    if !found {
      result[resultIndex] := arr[i];
      resultIndex := resultIndex + 1;
    }
    i := i + 1;
  }
  
  // Sort the result array using bubble sort
  var k := 0;
  while k < result.Length - 1
    invariant 0 <= k < result.Length
    invariant forall m :: 0 <= m < k ==> result[m] <= result[m + 1]
  {
    var l := k + 1;
    while l < result.Length
      invariant k + 1 <= l <= result.Length
      invariant forall m :: 0 <= m < k ==> result[m] <= result[m + 1]
    {
      if result[k] > result[l] {
        var temp := result[k];
        result[k] := result[l];
        result[l] := temp;
      }
      l := l + 1;
    }
    k := k + 1;
  }
}
// </vc-code>
