predicate sorted(a: array<int>)
   requires a != null
   reads a
{
   forall j, k :: 0 <= j < k < a.Length ==> a[j] <= a[k]
}

// <vc-helpers>
// No helper predicates needed - sorted is already defined in preamble
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
    var high := a.Length;
    
    while low < high
        invariant 0 <= low <= high <= a.Length
        invariant forall k :: 0 <= k < low ==> a[k] < value
        invariant forall k :: high <= k < a.Length ==> a[k] > value
    {
        var mid := (low + high) / 2;
        
        if a[mid] < value {
            low := mid + 1;
        } else if a[mid] > value {
            high := mid;
        } else {
            return mid;
        }
    }
    
    return -1;
}
// </vc-code>

