//ATOM_PLACEHOLDER_SplitPoint

// SPEC 

method SelectionSort(a: array<int>)
    modifies a
    ensures forall i,j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
    ensures multiset(a[..]) == old(multiset(a[..]))
{
}


//ATOM_PLACEHOLDER_QuickSort

twostate predicate SwapFrame(a: array<int>, lo: int, hi: int)
    requires 0 <= lo <= hi <= a.Length
    reads a
{
    (forall i :: 0 <= i < lo || hi <= i < a.Length ==> a[i] == old(a[i])) && multiset(a[..]) == old(multiset(a[..]))
}

//ATOM_PLACEHOLDER_QuickSortAux

//ATOM_PLACEHOLDER_Partition

