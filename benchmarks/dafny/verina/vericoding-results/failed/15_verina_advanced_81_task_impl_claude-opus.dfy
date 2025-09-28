// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
predicate InArray(arr: array<int>, x: int, n: int)
  reads arr
  requires 0 <= n <= arr.Length
{
  exists i :: 0 <= i < n && arr[i] == x
}

/* helper modified by LLM (iteration 5): Fixed postconditions and implementation */
method MergeSort(arr: array<int>) returns (sorted: array<int>)
  ensures sorted.Length == arr.Length
  ensures forall i :: 0 <= i < sorted.Length - 1 ==> sorted[i] <= sorted[i + 1]
  ensures multiset(arr[..]) == multiset(sorted[..])
  decreases arr.Length
{
  if arr.Length <= 1 {
    sorted := new int[arr.Length];
    if arr.Length == 1 {
      sorted[0] := arr[0];
    }
  } else {
    var mid := arr.Length / 2;
    var left := new int[mid];
    var right := new int[arr.Length - mid];
    
    var i := 0;
    while i < mid
      invariant 0 <= i <= mid
      invariant forall j :: 0 <= j < i ==> left[j] == arr[j]
    {
      left[i] := arr[i];
      i := i + 1;
    }
    
    i := 0;
    while i < arr.Length - mid
      invariant 0 <= i <= arr.Length - mid
      invariant forall j :: 0 <= j < i ==> right[j] == arr[mid + j]
    {
      right[i] := arr[mid + i];
      i := i + 1;
    }
    
    assert multiset(left[..]) + multiset(right[..]) == multiset(arr[..]);
    
    var sortedLeft := MergeSort(left);
    var sortedRight := MergeSort(right);
    sorted := Merge(sortedLeft, sortedRight);
    
    assert multiset(sorted[..]) == multiset(sortedLeft[..]) + multiset(sortedRight[..]);
    assert multiset(sortedLeft[..]) == multiset(left[..]);
    assert multiset(sortedRight[..]) == multiset(right[..]);
  }
}

/* helper modified by LLM (iteration 5): Fixed merge logic and invariants */
method Merge(left: array<int>, right: array<int>) returns (merged: array<int>)
  requires forall i :: 0 <= i < left.Length - 1 ==> left[i] <= left[i + 1]
  requires forall i :: 0 <= i < right.Length - 1 ==> right[i] <= right[i + 1]
  ensures merged.Length == left.Length + right.Length
  ensures forall i :: 0 <= i < merged.Length - 1 ==> merged[i] <= merged[i + 1]
  ensures multiset(left[..]) + multiset(right[..]) == multiset(merged[..])
{
  merged := new int[left.Length + right.Length];
  var i, j, k := 0, 0, 0;
  
  while k < merged.Length
    invariant 0 <= i <= left.Length
    invariant 0 <= j <= right.Length
    invariant k == i + j
    invariant forall p :: 0 <= p < k - 1 ==> merged[p] <= merged[p + 1]
    invariant i < left.Length && j < right.Length && k > 0 ==> 
              merged[k-1] <= left[i] && merged[k-1] <= right[j]
    invariant i == left.Length && j < right.Length && k > 0 ==> merged[k-1] <= right[j]
    invariant j == right.Length && i < left.Length && k > 0 ==> merged[k-1] <= left[i]
    invariant multiset(merged[..k]) == multiset(left[..i]) + multiset(right[..j])
  {
    if i < left.Length && (j >= right.Length || left[i] <= right[j]) {
      merged[k] := left[i];
      i := i + 1;
    } else {
      merged[k] := right[j];
      j := j + 1;
    }
    k := k + 1;
  }
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
  /* code modified by LLM (iteration 5): Fixed syntax error - proper if-then braces */
  var sorted := MergeSort(arr);
  
  if sorted.Length == 0 {
    result := new int[0];
    return;
  }
  
  var count := 1;
  var i := 1;
  while i < sorted.Length
    invariant 1 <= i <= sorted.Length
    invariant 1 <= count <= i
    invariant count == 1 + (set k | 0 < k < i && sorted[k] != sorted[k-1] :: k) | |
  {
    if sorted[i] != sorted[i - 1] {
      count := count + 1;
    }
    i := i + 1;
  }
  
  result := new int[count];
  result[0] := sorted[0];
  var j := 1;
  i := 1;
  while i < sorted.Length && j < count
    invariant 1 <= i <= sorted.Length
    invariant 1 <= j <= count
    invariant j <= i
    invariant forall k :: 0 <= k < j - 1 ==> result[k] < result[k + 1]
    invariant j > 0 ==> result[j-1] == sorted[i-1]
    invariant forall k :: 0 <= k < j ==> result[k] in sorted[..i]
    invariant forall x :: x in result[..j] ==> x in sorted[..]
  {
    if sorted[i] != sorted[i - 1] {
      result[j] := sorted[i];
      j := j + 1;
    }
    i := i + 1;
  }
  
  assert multiset(sorted[..]) == multiset(arr[..]);
  assert forall x :: x in result[..] ==> x in sorted[..];
  assert forall x :: x in sorted[..] ==> x in result[..];
}
// </vc-code>
