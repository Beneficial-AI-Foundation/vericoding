twostate predicate Preserved(a: array<int>, left: nat, right: nat)
    reads a
    requires left <= right <= a.Length
{
    multiset(a[left..right]) == multiset(old(a[left..right]))
}

ghost predicate Ordered(a: array<int>, left: nat, right: nat)
    reads a
    requires left <= right <= a.Length
{
    forall i: nat :: 0 < left <= i < right ==> a[i-1] <= a[i]
}

twostate predicate Sorted(a: array<int>)
    reads a
{
    Ordered(a,0,a.Length) && Preserved(a,0,a.Length)
}

// <vc-helpers>
// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method SelectionnSort(a: array<int>)
    modifies a
    ensures Sorted(a)
// </vc-spec>
// <vc-code>
{
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant Ordered(a, 0, i)
    invariant Preserved(a, 0, a.Length)
  {
    var minIdx := i;
    var j := i + 1;
    while j < a.Length
      invariant i <= minIdx < a.Length
      invariant i <= j <= a.Length
      invariant forall k: nat :: i <= k < j ==> a[minIdx] <= a[k]
    {
      if a[j] < a[minIdx] {
        minIdx := j;
      }
      j := j + 1;
    }
    var temp := a[i];
    a[i] := a[minIdx];
    a[minIdx] := temp;
    i := i + 1;
  }
}
// </vc-code>

