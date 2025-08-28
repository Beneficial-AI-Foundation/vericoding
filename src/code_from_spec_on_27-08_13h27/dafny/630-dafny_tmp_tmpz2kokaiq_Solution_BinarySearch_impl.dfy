function sorted(a: array<int>) : bool
    reads a
{
   forall i,j : int :: 0 <= i < j < a.Length ==> a[i] <= a[j]
}

// <vc-helpers>
lemma MidpointProperty(low: int, high: int)
    ensures low <= high ==> low <= (low + high) / 2 <= high
{
    if low <= high {
        assert low <= (low + high) / 2;
        assert (low + high) / 2 <= high;
    }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method BinarySearch(a: array<int>, x: int) returns (index: int)
    requires sorted(a)
    ensures 0 <= index < a.Length ==> a[index] == x
    ensures index == -1 ==> forall i : int :: 0 <= i < a.Length ==> a[i] != x
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    var low := 0;
    var high := a.Length - 1;
    while low <= high
        invariant 0 <= low <= a.Length
        invariant -1 <= high < a.Length
        invariant forall i :: 0 <= i < low ==> a[i] < x
        invariant forall i :: high < i < a.Length ==> a[i] > x
    {
        var mid := (low + high) / 2;
        MidpointProperty(low, high);
        if a[mid] == x {
            return mid;
        } else if a[mid] < x {
            low := mid + 1;
        } else {
            high := mid - 1;
        }
    }
    return -1;
}
// </vc-code>
