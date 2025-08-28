// <vc-helpers>
lemma ZeroImpliesLeftmostZero(a: array<int>, i: int, j: int)
  requires forall k :: 0 <= k < a.Length ==> 0 <= a[k]
  requires forall k :: 0 < k < a.Length ==> a[k-1]-1 <= a[k]
  requires 0 <= i < j < a.Length
  requires a[j] == 0
  ensures a[i] == 0
{
  if a[i] != 0 {
    assert a[i] >= 1;
    IncrementalLowerBound(a, i, j);
    assert a[j] >= a[i] + (j - i);
    assert a[j] >= 1 + (j - i);
    assert a[j] > 0;
    assert false;
  }
}

lemma IncrementalLowerBound(a: array<int>, start: int, end: int)
  requires forall k :: 0 <= k < a.Length ==> 0 <= a[k]
  requires forall k :: 0 < k < a.Length ==> a[k-1]-1 <= a[k]
  requires 0 <= start < end < a.Length
  ensures a[end] >= a[start] + (end - start)
{
  if start + 1 == end {
    assert a[end-1] - 1 <= a[end];
    assert a[start] - 1 <= a[end];
    assert a[start] <= a[end] + 1;
    assert end - start == 1;
    assert a[end] >= a[start] - 1;
    assert a[end] + 1 >= a[start];
    assert a[end] >= a[start] + (end - start);
  } else {
    var mid := end - 1;
    IncrementalLowerBound(a, start, mid);
    assert a[mid] >= a[start] + (mid - start);
    assert a[end-1] - 1 <= a[end];
    assert a[mid] - 1 <= a[end];
    assert a[start] + (mid - start) - 1 <= a[end];
    assert (mid - start) - 1 + 1 == mid - start;
    assert mid - start + 1 == end - start;
    assert a[end] >= a[start] + (end - start);
  }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method FindZero(a: array<int>) returns (index: int)
   requires a != null
   requires forall i :: 0 <= i < a.Length ==> 0 <= a[i]
   requires forall i :: 0 < i < a.Length ==> a[i-1]-1 <= a[i]
   ensures index < 0  ==> forall i :: 0 <= i < a.Length ==> a[i] != 0
   ensures 0 <= index ==> index < a.Length && a[index] == 0
// </vc-spec>
// </vc-spec>

// <vc-code>
{
  if a.Length == 0 {
    return -1;
  }
  
  if a[0] == 0 {
    return 0;
  }
  
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant forall j :: 0 <= j < i ==> a[j] != 0
  {
    if a[i] == 0 {
      return i;
    }
    i := i + 1;
  }
  
  return -1;
}
// </vc-code>
