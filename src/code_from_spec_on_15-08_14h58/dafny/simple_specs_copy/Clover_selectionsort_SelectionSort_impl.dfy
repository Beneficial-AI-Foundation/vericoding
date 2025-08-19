//IMPL 
method SelectionSort(a: array<int>)
 modifies a
 ensures forall i,j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
 ensures multiset(a[..]) == old(multiset(a[..]))
{
    var i := 0;
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant forall k,l :: 0 <= k < l < i ==> a[k] <= a[l]
        invariant forall k,l :: 0 <= k < i <= l < a.Length ==> a[k] <= a[l]
        invariant multiset(a[..]) == old(multiset(a[..]))
    {
        var minIndex := i;
        var j := i + 1;
        
        while j < a.Length
            invariant i <= minIndex < a.Length
            invariant i <= j <= a.Length
            invariant forall k :: i <= k < j ==> a[minIndex] <= a[k]
        {
            if a[j] < a[minIndex] {
                minIndex := j;
            }
            j := j + 1;
        }
        
        if minIndex != i {
            a[i], a[minIndex] := a[minIndex], a[i];
        }
        
        i := i + 1;
    }
}