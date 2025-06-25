// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

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
    requires
        0 <= lo <= hi <= a.len(),
        SplitPoint(a, lo) && SplitPoint(a, hi)
    modifies a,
        0 <= lo < hi <= a.len(),
        SplitPoint(a, lo) && SplitPoint(a, hi)
    modifies a
    ensures
        forall i,j :: lo <= i < j < hi ==> a.spec_index(i) <= a.spec_index(j),
        SwapFrame(a, lo, hi),
        SplitPoint(a, lo) && SplitPoint(a, hi),
        lo <= p < hi,
        forall i :: lo <= i < p ==> a.spec_index(i) < a.spec_index(p),
        forall i :: p <= i < hi ==> a.spec_index(p) <= a.spec_index(i),
        SplitPoint(a, lo) && SplitPoint(a, hi),
        SwapFrame(a, lo, hi)
{
    return 0;
}

}