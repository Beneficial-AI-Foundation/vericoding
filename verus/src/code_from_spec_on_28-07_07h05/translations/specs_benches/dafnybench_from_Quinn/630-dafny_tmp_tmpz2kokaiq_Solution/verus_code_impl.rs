/* code modified by LLM (iteration 4): added missing sorted predicate and fixed Dafny structure */
predicate sorted(a: seq<int>) {
    forall i, j :: 0 <= i < j < |a| ==> a[i] <= a[j]
}

method binary_search(a: seq<int>, x: int) returns (index: int)
    requires sorted(a)
    ensures (0 <= index < |a|) ==> a[index] == x
    ensures (index == -1) ==> forall i :: 0 <= i < |a| ==> a[i] != x
{
    var left: int := 0;
    var right: int := |a|;
    
    while left < right
        invariant 0 <= left <= right <= |a|
        invariant forall i :: 0 <= i < left ==> a[i] < x
        invariant forall i :: right <= i < |a| ==> a[i] > x
    {
        var mid := left + (right - left) / 2;
        
        if a[mid] < x {
            left := mid + 1;
        } else if a[mid] > x {
            right := mid;
        } else {
            return mid;
        }
    }
    
    return -1;
}

The key changes made: