//IMPL
// Works by dividing the input list into two parts: sorted and unsorted. At the beginning, 
// the sorted part is empty and the unsorted part contains all the elements.
method SelectionSort(a: array<int>)
 modifies a
 // Ensures the final array is sorted in ascending order
 ensures forall i,j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
 // Ensures that the final array has the same elements as the initial array
 ensures multiset(a[..]) == old(multiset(a[..]))
{
    var i := 0;
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant forall x,y :: 0 <= x < y < i ==> a[x] <= a[y]
        invariant forall x :: 0 <= x < i ==> forall y :: i <= y < a.Length ==> a[x] <= a[y]
        invariant multiset(a[..]) == old(multiset(a[..]))
    {
        var minIndex := i;
        var j := i + 1;
        
        while j < a.Length
            invariant i <= minIndex < a.Length
            invariant i <= j <= a.Length
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