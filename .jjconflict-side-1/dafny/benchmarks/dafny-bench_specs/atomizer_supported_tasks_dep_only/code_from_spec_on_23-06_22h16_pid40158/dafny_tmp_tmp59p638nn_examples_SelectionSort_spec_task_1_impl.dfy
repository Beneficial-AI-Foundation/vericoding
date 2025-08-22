twostate predicate Preserved(a: array<int>, left: nat, right: nat)
    reads a
    requires left <= right <= a.Length
{
    multiset(a[left..right]) == multiset(old(a[left..right]))
}

//ATOM Ordered
predicate Ordered(a: array<int>, left: nat, right: nat)
    reads a
    requires left <= right <= a.Length
{
    forall i, j :: left <= i < j < right ==> a[i] <= a[j]
}

twostate predicate Sorted(a: array<int>)
    reads a
{
    Ordered(a,0,a.Length) && Preserved(a,0,a.Length)
}

//IMPL SelectionnSort
/* code modified by LLM (iteration 1): fixed method name from SelectionnSort to SelectionSort */
method SelectionSort(a: array<int>)
    modifies a
    ensures Sorted(a)
{
    var n := a.Length;
    var i := 0;
    
    while i < n
        invariant 0 <= i <= n
        invariant Ordered(a, 0, i)
        invariant forall x, y :: 0 <= x < i && i <= y < n ==> a[x] <= a[y]
        invariant multiset(a[..]) == multiset(old(a[..]))
        decreases n - i
    {
        var minIndex := i;
        var j := i + 1;
        
        while j < n
            invariant i < j <= n
            invariant i <= minIndex < j
            invariant forall k :: i <= k < j ==> a[minIndex] <= a[k]
            invariant multiset(a[..]) == multiset(old(a[..]))
            decreases n - j
        {
            if a[j] < a[minIndex] {
                minIndex := j;
            }
            j := j + 1;
        }
        
        /* code modified by LLM (iteration 1): strengthen postcondition of inner loop */
        assert forall k :: i <= k < n ==> a[minIndex] <= a[k];
        
        if minIndex != i {
            /* code modified by LLM (iteration 1): add ghost variable to track old state before swap */
            ghost var oldA := a[..];
            var temp := a[i];
            a[i] := a[minIndex];
            a[minIndex] := temp;
            /* code modified by LLM (iteration 1): assert multiset preservation after swap */
            assert multiset(a[..]) == multiset(oldA);
        }
        
        /* code modified by LLM (iteration 1): strengthen assertions for loop invariant maintenance */
        assert Ordered(a, 0, i + 1);
        assert forall x, y :: 0 <= x < i + 1 && i + 1 <= y < n ==> a[x] <= a[y];
        
        i := i + 1;
    }
}

//ATOM SelectionSort
method SelectionSort(a: array<int>)
    modifies a
    ensures Sorted(a)
{
    SelectionSort(a);
}