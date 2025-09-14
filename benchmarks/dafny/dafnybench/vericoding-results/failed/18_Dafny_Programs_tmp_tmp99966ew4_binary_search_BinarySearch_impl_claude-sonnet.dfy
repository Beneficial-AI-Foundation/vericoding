predicate sorted(a: array<int>)
   requires a != null
   reads a
{
   forall j, k :: 0 <= j < k < a.Length ==> a[j] <= a[k]
}

// <vc-helpers>
lemma SortedSlice(a: array<int>, low: int, high: int)
    requires sorted(a)
    requires 0 <= low <= high <= a.Length
    ensures forall j, k :: low <= j < k < high ==> a[j] <= a[k]
{
}

lemma SortedImpliesOrder(a: array<int>, i: int, j: int)
    requires sorted(a)
    requires 0 <= i < j < a.Length
    ensures a[i] <= a[j]
{
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
    if a.Length == 0 {
        return -1;
    }
    
    var low := 0;
    var high := a.Length;
    
    while low < high
        invariant 0 <= low <= high <= a.Length
        invariant forall k :: 0 <= k < low ==> a[k] < value
        invariant forall k :: high <= k < a.Length ==> a[k] > value
    {
        var mid := low + (high - low) / 2;
        
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

