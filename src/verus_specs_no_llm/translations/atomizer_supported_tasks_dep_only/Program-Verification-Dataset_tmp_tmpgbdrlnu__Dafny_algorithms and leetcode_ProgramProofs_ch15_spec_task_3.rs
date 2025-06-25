// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

spec fn SplitPoint(a: Vec<int>, n: int)
    reads a
    requires 0 <= n <= n

{
    forall i, j: : 0 <= i < n <= j < a.Length ==> a[i] <= a[j]
}


//ATOM_PLACEHOLDER_SelectionSort

//ATOM_PLACEHOLDER_QuickSort

twostate predicate SwapFrame(a: array<int>, lo: int, hi: int)
    requires 0 <= lo <= hi <= a.Length
    reads a
{
    (forall i :: 0 <= i < lo || hi <= i < a.Length ==> a[i] == old(a[i])) && multiset(a[..]) == old(multiset(a[..]))
}

// SPEC 

method QuickSortAux(a: array<int>, lo: int, hi: int)
    requires 0 <= lo <= hi <= a.Length
    requires SplitPoint(a, lo) && SplitPoint(a, hi)
    modifies a
    ensures forall i, j: : lo <= i < j < hi ==> a[i] <= a[j]
    ensures SwapFrame(a, lo, hi)
    ensures SplitPoint(a, lo) && SplitPoint(a, hi) -> bool {
    
}

fn QuickSortAux(a: Vec<int>, lo: int, hi: int)
    requires 0 <= lo <= hi <= a.Length
    requires SplitPoint(a, lo) && SplitPoint(a, hi)
    modifies a
    ensures forall i, j: : lo <= i < j < hi ==> a[i] <= a[j]
    ensures SwapFrame(a, lo, hi)
    ensures SplitPoint(a, lo) && SplitPoint(a, hi)
{
}


// SPEC 

method Partition(a: Vec<int>, lo: int, hi: int) -> (p: int)
    requires 0 <= lo <= hi <= a.len(),
             SplitPoint(a, lo) and SplitPoint(a, hi)
    modifies a,
             0 <= lo < hi <= a.len(),
             SplitPoint(a, lo) and SplitPoint(a, hi)
    modifies a
    ensures forall|i: int, j: int| lo <= i < j < hi ==> a[i] <= a[j],
            SwapFrame(a, lo, hi),
            SplitPoint(a, lo) and SplitPoint(a, hi),
            lo <= p < hi,
            forall|i: int| lo <= i < p ==> a[i] < a[p],
            forall|i: int| p <= i < hi ==> a[p] <= a[i],
            SplitPoint(a, lo) and SplitPoint(a, hi),
            SwapFrame(a, lo, hi)
{
}

}