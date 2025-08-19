//IMPL 
method SelectionSort(a: array<int>)
 modifies a
 ensures forall i,j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
 ensures multiset(a[..]) == old(multiset(a[..]))
{
    if a.Length <= 1 {
        return;
    }
    
    var i := 0;
    while i < a.Length - 1
        invariant 0 <= i <= a.Length - 1
        invariant forall x,y :: 0 <= x < y < i ==> a[x] <= a[y]
        invariant forall x,y :: 0 <= x < i && i <= y < a.Length ==> a[x] <= a[y]
        invariant multiset(a[..]) == old(multiset(a[..]))
    {
        var minIndex := i;
        var j := i + 1;
        
        while j < a.Length
            invariant i < j <= a.Length
            invariant i <= minIndex < j
            invariant forall k :: i <= k < j ==> a[minIndex] <= a[k]
            invariant multiset(a[..]) == old(multiset(a[..]))
        {
            if a[j] < a[minIndex] {
                minIndex := j;
            }
            j := j + 1;
        }
        
        if minIndex != i {
            var temp := a[i];
            a[i] := a[minIndex];
            a[minIndex] := temp;
        }
        
        i := i + 1;
    }
}