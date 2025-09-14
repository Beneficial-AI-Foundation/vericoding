predicate sorted (a: array<int>)

    reads a
{
    sortedA(a, a.Length)
}

predicate sortedA (a: array<int>, i: int)

    requires 0 <= i <= a.Length
    reads a
{
    forall k :: 0 < k < i ==> a[k-1] <= a[k]
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method lookForMin (a: array<int>, i: int) returns (m: int)

    requires 0 <= i < a.Length
    ensures i <= m < a.Length
    ensures forall k :: i <= k < a.Length ==> a[k] >= a[m]
// </vc-spec>
// <vc-code>
{
  var j := i;
  var t := i + 1;
  while t < a.Length
    invariant i <= j < t <= a.Length
    invariant forall k :: i <= k < t ==> a[j] <= a[k]
    decreases a.Length - t
  {
    if a[t] < a[j] {
      forall k | i <= k < t
        ensures a[t] <= a[k]
      {
        assert a[j] <= a[k];
        assert a[t] < a[j];
        assert a[t] <= a[k];
      }
      j := t;
    }
    t := t + 1;
  }
  m := j;
}
// </vc-code>

