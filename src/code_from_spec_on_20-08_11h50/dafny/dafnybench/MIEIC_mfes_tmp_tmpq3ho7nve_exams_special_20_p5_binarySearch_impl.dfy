predicate sorted<T(0)>(a: array<T>, n: nat) 
    requires n <= a.Length
    reads a
{
    forall i,j :: 0 <= i < j < n ==> a[i] <= a[j]
}

// Use binary search to find an appropriate position to insert a value 'x'
// in a sorted array 'a', so that it remains sorted.

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method binarySearch<T>(a: array<T>, x: T) returns (index: int) 
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
    var left := 0;
    var right := a.Length;
    
    while left < right
        invariant 0 <= left <= right <= a.Length
        invariant forall i :: 0 <= i < left ==> a[i] <= x
        invariant forall i :: right <= i < a.Length ==> a[i] >= x
        invariant sorted(a, a.Length)
        decreases right - left
    {
        var mid := left + (right - left) / 2;
        
        if a[mid] <= x {
            left := mid + 1;
        } else {
            right := mid;
        }
    }
    
    index := left;
}
// </vc-code>

// Simple test cases to check the post-condition