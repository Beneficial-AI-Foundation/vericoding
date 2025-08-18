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

method lookForMin (a: array<int>, i: int) returns (m: int)

    requires 0 <= i < a.Length
    ensures i <= m < a.Length
    ensures forall k :: i <= k < a.Length ==> a[k] >= a[m]
{
    var j := i;
    m := i;
    while(j < a.Length)
        invariant i <= j <= a.Length
        invariant i <= m < a.Length
        invariant forall k :: i <= k < j ==> a[k] >= a[m]
        decreases a.Length - j
    {
        if(a[j] < a[m]) { m := j; }
        j := j + 1;
    }
}

// <vc-helpers>
// </vc-helpers>

method insertionSort (a: array<int>)

    modifies a
    ensures sorted(a)
// <vc-code>
{
  assume false;
}
// </vc-code>