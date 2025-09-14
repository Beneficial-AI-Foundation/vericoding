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
// No new helper code and proofs needed for verification
// </vc-helpers>

// <vc-spec>
method lookForMin (a: array<int>, i: int) returns (m: int)

    requires 0 <= i < a.Length
    ensures i <= m < a.Length
    ensures forall k :: i <= k < a.Length ==> a[k] >= a[m]
// </vc-spec>
// <vc-code>
{
  var minIdx := i;
  var j := i + 1;
  while (j < a.Length)
    invariant i <= j <= a.Length
    invariant i <= minIdx < a.Length
    invariant forall k :: i <= k < j ==> a[k] >= a[minIdx]
    decreases a.Length - j
  {
    if (a[j] < a[minIdx]) {
      minIdx := j;
    }
    j := j + 1;
  }
  m := minIdx;
}
// </vc-code>

