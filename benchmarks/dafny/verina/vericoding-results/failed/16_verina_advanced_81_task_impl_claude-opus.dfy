// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed multiset preservation and merge invariants */
predicate InArray(arr: array<int>, x: int, n: int)
  requires 0 <= n <= arr.Length
  reads arr
{
  exists i :: 0 <= i < n && arr[i] == x
}

method MergeSort(arr: array<int>) returns (sorted: array<int>)
  ensures sorted.Length == arr.Length
  ensures multiset(sorted[..]) == multiset(arr[..])
  ensures forall i :: 0 <= i < sorted.Length - 1 ==> sorted[i] <= sorted[i + 1]
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
    assert left[..] == arr[..mid];
    
    i := 0;
    while i < arr.Length - mid
      invariant 0 <= i <= arr.Length - mid
      invariant forall j :: 0 <= j < i ==> right[j] == arr[mid + j]
    {
      right[i] := arr[mid + i];
      i := i + 1;
    }
    assert right[..] == arr[mid..];
    assert multiset(left[..]) + multiset(right[..]) == multiset(arr[..]);
    
    var sortedLeft := MergeSort(left);
    var sortedRight := MergeSort(right);
    sorted := Merge(sortedLeft, sortedRight);
    assert multiset(sorted[..]) == multiset(sortedLeft[..]) + multiset(sortedRight[..]);
    assert multiset(sorted[..]) == multiset(left[..]) + multiset(right[..]);
    assert multiset(sorted[..]) == multiset(arr[..]);
  }
}

method Merge(left: array<int>, right: array<int>) returns (merged: array<int>)
  requires forall i :: 0 <= i < left.Length - 1 ==> left[i] <= left[i + 1]
  requires forall i :: 0 <= i < right.Length - 1 ==> right[i] <= right[i + 1]
  ensures merged.Length == left.Length + right.Length
  ensures multiset(merged[..]) == multiset(left[..]) + multiset(right[..])
  ensures forall i :: 0 <= i < merged.Length - 1 ==> merged[i] <= merged[i + 1]
{
  merged := new int[left.Length + right.Length];
  var i, j, k := 0, 0, 0;
  
  while k < merged.Length
    invariant 0 <= i <= left.Length
    invariant 0 <= j <= right.Length
    invariant k == i + j
    invariant multiset(merged[..k]) == multiset(left[..i]) + multiset(right[..j])
    invariant forall p :: 0 <= p < k - 1 ==> merged[p] <= merged[p + 1]
    invariant k > 0 && i < left.Length ==> merged[k - 1] <= left[i]
    invariant k > 0 && j < right.Length ==> merged[k - 1] <= right[j]
  {
    if i == left.Length {
      merged[k] := right[j];
      j := j + 1;
    } else if j == right.Length {
      merged[k] := left[i];
      i := i + 1;
    } else if left[i] <= right[j] {
      merged[k] := left[i];
      i := i + 1;
    } else {
      merged[k] := right[j];
      j := j + 1;
    }
    k := k + 1;
  }
  assert i == left.Length && j == right.Length;
  assert k == merged.Length;
  assert multiset(merged[..]) == multiset(left[..]) + multiset(right[..]);
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
  /* code modified by LLM (iteration 5): Simplified unique extraction with clearer invariants */
  var sorted := MergeSort(arr);
  
  if sorted.Length == 0 {
    result := new int[0];
  } else {
    // Count unique elements
    var count := 1;
    var i := 1;
    while i < sorted.Length
      invariant 1 <= i <= sorted.Length
      invariant 1 <= count <= i
    {
      if sorted[i] != sorted[i - 1] {
        count := count + 1;
      }
      i := i + 1;
    }
    
    // Create result with unique elements
    result := new int[count];
    result[0] := sorted[0];
    var pos := 1;
    i := 1;
    
    while i < sorted.Length
      invariant 1 <= i <= sorted.Length
      invariant 1 <= pos <= count
      invariant pos <= i
      invariant forall j :: 0 <= j < pos - 1 ==> result[j] < result[j + 1]
      invariant pos > 0 ==> result[pos - 1] <= sorted[i - 1]
    {
      if sorted[i] != sorted[i - 1] {
        if pos < count {
          result[pos] := sorted[i];
          pos := pos + 1;
        }
      }
      i := i + 1;
    }
    
    // Verify postconditions
    assert forall x :: x in sorted[..] ==> x in result[..];
    assert forall x :: x in result[..] ==> x in sorted[..];
    assert multiset(sorted[..]) == multiset(arr[..]);
    assert forall x :: x in arr[..] ==> x in sorted[..];
    assert forall x :: x in sorted[..] ==> x in arr[..];
  }
}
// </vc-code>
