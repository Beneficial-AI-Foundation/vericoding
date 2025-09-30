type T = int // example

 // Partitions a nonempty array 'a', by reordering the elements in the array,
// so that elements smaller than a chosen pivot are placed to the left of the
// pivot, and values greater or equal than the pivot are placed to the right of 
// the pivot. Returns the pivot position.

// <vc-helpers>
ghost predicate IsPartitioned(a: array<T>, pivotPos: int, pivot: T)
    reads a
    requires 0 <= pivotPos < a.Length
{
    a[pivotPos] == pivot &&
    (forall i :: 0 <= i < pivotPos ==> a[i] < pivot) &&
    (forall i :: pivotPos < i < a.Length ==> a[i] >= pivot)
}
// </vc-helpers>

// <vc-spec>
method partition(a: array<T>) returns(pivotPos: int) 
    requires a.Length > 0
    ensures 0 <= pivotPos < a.Length
    ensures forall i :: 0 <= i < pivotPos ==> a[i] < a[pivotPos]
    ensures forall i :: pivotPos < i < a.Length ==> a[i] >= a[pivotPos]
    ensures multiset(a[..]) == multiset(old(a[..]))
    modifies a
// </vc-spec>
// <vc-code>
{
    var pivot := a[0];
    var i := 1;
    var j := 1;
    
    while j < a.Length
        invariant 1 <= i <= j <= a.Length
        invariant a[0] == pivot
        invariant forall k :: 1 <= k < i ==> a[k] < pivot
        invariant forall k :: i <= k < j ==> a[k] >= pivot
        invariant multiset(a[..]) == multiset(old(a[..]))
    {
        if a[j] < pivot {
            if i != j {
                var temp := a[i];
                a[i] := a[j];
                a[j] := temp;
            }
            i := i + 1;
        }
        j := j + 1;
    }
    
    // Move pivot to its final position
    pivotPos := i - 1;
    var temp := a[0];
    a[0] := a[pivotPos];
    a[pivotPos] := temp;
    
    return pivotPos;
}
// </vc-code>

