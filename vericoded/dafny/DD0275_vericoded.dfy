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
    m := i;
    var j := i + 1;
    
    while j < a.Length
        invariant i <= m < j <= a.Length
        invariant forall k :: i <= k < j ==> a[k] >= a[m]
    {
        if a[j] < a[m] {
            m := j;
        }
        j := j + 1;
    }
}
// </vc-code>

