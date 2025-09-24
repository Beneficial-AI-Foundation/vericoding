// <vc-preamble>
type T = int // for demo purposes, but could be another type
predicate sorted(a: array<T>, n: nat) 
    requires n <= a.Length
    reads a
{
    forall i,j :: 0 <= i < j < n ==> a[i] <= a[j]
}

// Use binary search to find an appropriate position to insert a value 'x'
// in a sorted array 'a', so that it remains sorted.
// </vc-preamble>

// <vc-helpers>
// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method binarySearch(a: array<T>, x: T) returns (index: int) 
    requires sorted(a, a.Length)
    ensures sorted(a, a.Length)
    //ensures a[..] == old(a)[..]
    ensures 0 <= index <= a.Length
    //ensures forall i :: 0 <= i < index ==> a[i] <= x
    //ensures forall i :: index <= i < a.Length ==> a[i] >= x

    ensures index > 0 ==> a[index-1] <= x
    ensures index < a.Length ==> a[index] >= x
// </vc-spec>
// <vc-code>
{
    var low, high := 0, a.Length;
    while low < high 
        decreases high-low
        invariant 0 <= low <= high <= a.Length
        invariant low > 0 ==> a[low-1] <= x
        invariant high < a.Length ==> a[high] >= x

    {
        var mid := low + (high - low) / 2;
        if {
            case a[mid] < x => low := mid + 1;
            case a[mid] > x => high := mid;
            case a[mid] == x => return mid;
        }
    }
    return low;
}
// </vc-code>

// Simple test cases to check the post-condition