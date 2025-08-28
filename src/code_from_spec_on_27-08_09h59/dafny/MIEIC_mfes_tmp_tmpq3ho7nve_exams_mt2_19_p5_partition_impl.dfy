type T = int // example

 // Partitions a nonempty array 'a', by reordering the elements in the array,
// so that elements smaller than a chosen pivot are placed to the left of the
// pivot, and values greater or equal than the pivot are placed to the right of 
// the pivot. Returns the pivot position.

// <vc-helpers>
lemma MultisetPreservation(a: array<T>, old_contents: seq<T>, i: int, j: int, new_contents: seq<T>)
    requires 0 <= i < |old_contents|
    requires 0 <= j < |old_contents|
    requires |new_contents| == |old_contents|
    requires new_contents == old_contents[i := old_contents[j]][j := old_contents[i]]
    ensures multiset(new_contents) == multiset(old_contents)
{
    if i != j {
        assert multiset(new_contents) == multiset(old_contents);
    }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method partition(a: array<T>) returns(pivotPos: int) 
    requires a.Length > 0
    ensures 0 <= pivotPos < a.Length
    ensures forall i :: 0 <= i < pivotPos ==> a[i] < a[pivotPos]
    ensures forall i :: pivotPos < i < a.Length ==> a[i] >= a[pivotPos]
    ensures multiset(a[..]) == multiset(old(a[..]))
    modifies a
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    if a.Length == 1 {
        return 0;
    }
    
    var pivot := a[0];
    var left := 0;
    var right := a.Length - 1;
    
    while left < right
        invariant 0 <= left <= a.Length
        invariant 0 <= right < a.Length
        invariant forall i :: 0 <= i < left ==> a[i] < pivot
        invariant forall i :: right < i < a.Length ==> a[i] >= pivot
        invariant multiset(a[..]) == multiset(old(a[..]))
        decreases right - left
    {
        while left < right && a[left] < pivot
            invariant 0 <= left <= a.Length
            invariant 0 <= right < a.Length
            invariant forall i :: 0 <= i < left ==> a[i] < pivot
            invariant forall i :: right < i < a.Length ==> a[i] >= pivot
            invariant multiset(a[..]) == multiset(old(a[..]))
        {
            left := left + 1;
        }
        
        while left < right && a[right] >= pivot
            invariant 0 <= left <= a.Length
            invariant 0 <= right < a.Length
            invariant forall i :: 0 <= i < left ==> a[i] < pivot
            invariant forall i :: right < i < a.Length ==> a[i] >= pivot
            invariant multiset(a[..]) == multiset(old(a[..]))
        {
            right := right - 1;
        }
        
        if left < right {
            var old_seq := a[..];
            var temp := a[left];
            a[left] := a[right];
            a[right] := temp;
            MultisetPreservation(a, old_seq, left, right, a[..]);
            left := left + 1;
            right := right - 1;
        }
    }
    
    if left < a.Length && a[left] < pivot {
        var old_seq := a[..];
        a[0] := a[left];
        a[left] := pivot;
        MultisetPreservation(a, old_seq, 0, left, a[..]);
        return left;
    } else {
        if left == 0 {
            return 0;
        } else {
            var old_seq := a[..];
            var pos := left - 1;
            a[0] := a[pos];
            a[pos] := pivot;
            MultisetPreservation(a, old_seq, 0, pos, a[..]);
            return pos;
        }
    }
}
// </vc-code>
