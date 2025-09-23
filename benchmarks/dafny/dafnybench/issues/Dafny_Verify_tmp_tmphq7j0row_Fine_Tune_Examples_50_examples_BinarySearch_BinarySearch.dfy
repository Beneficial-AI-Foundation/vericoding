// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method BinarySearch(a: array<int>, key: int) returns (n: int)
    requires forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
    ensures 0 <= n <= a.Length
    ensures forall i :: 0 <= i < n ==> a[i] < key
    ensures forall i :: n <= i < a.Length ==> key <= a[i]
// </vc-spec>
// <vc-code>
{
    var lo, hi := 0, a.Length;

    while lo < hi
        invariant 0 <= lo <= hi <= a.Length
        invariant forall i :: 0 <= i < lo ==> a[i] < key
        invariant forall i :: hi <= i < a.Length ==> key <= a[i]
    {
        var mid := (lo + hi) / 2;

        if a[mid] < key {
            lo := mid + 1;
        } else {
            hi := mid;
        }
    }

    n := lo;
}
// </vc-code>
