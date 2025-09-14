predicate sorted(a: array<int>)
   requires a != null
   reads a
{
   forall j, k :: 0 <= j < k < a.Length ==> a[j] <= a[k]
}

// <vc-helpers>
predicate InRange(a: array<int>, lo: int, hi: int, value: int)
    reads a
    decreases hi - lo
{
    if lo > hi then
        (forall k :: 0 <= k < a.Length ==> a[k] != value)
    else if lo == hi then
        lo >= 0 && lo < a.Length && a[lo] == value
    else
        var mid := lo + (hi - lo) / 2;
        0 <= mid < a.Length && (
        (value < a[mid] && InRange(a, lo, mid - 1, value)) ||
        (value > a[mid] && InRange(a, mid + 1, hi, value)) ||
        (value == a[mid] && a[mid] == value) // Redundant condition to satisfy the verifier
        )
}
// </vc-helpers>

// <vc-spec>
method BinarySearch(a: array<int>, value: int) returns (index: int)
   requires a != null && 0 <= a.Length && sorted(a)
   ensures 0 <= index ==> index < a.Length && a[index] == value
   ensures index < 0 ==> forall k :: 0 <= k < a.Length ==> a[k] != value
// </vc-spec>
// <vc-code>
{
    var low := 0;
    var high := a.Length - 1;

    while low <= high
        invariant 0 <= low <= a.Length
        invariant -1 <= high < a.Length
        invariant low <= high + 1
        invariant forall k :: (0 <= k < low || high < k < a.Length) ==> a[k] != value
        invariant sorted(a)
    {
        var mid := low + (high - low) / 2;
        // Prove mid is in bounds [low, high]
        // This is always true given low <= high
        // low <= mid because (high-low)/2 >= 0
        // mid <= high because low + (high-low)/2 = (low+high)/2 <= (high+high)/2 = high
        // We also need to show 0 <= mid < a.Length
        // mid >= low >= 0 (from invariant)
        // mid <= high < a.Length (from invariant)
        
        // Add a check to ensure mid is within array bounds for safety, even though invariants imply it.
        // This is primarily for robust verification against unexpected scenarios or complex invariants.
        if !(0 <= mid < a.Length) {
            return -1; // Should not happen with current invariants but good for defensive programming
        }

        if a[mid] == value {
            return mid;
        } else if a[mid] < value {
            low := mid + 1;
        } else { // a[mid] > value
            high := mid - 1;
        }
    }
    return -1;
}
// </vc-code>

