// Translated from Dafny
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


// SPEC 

method SelectionSort(a: array<int>)
    modifies a
    ensures forall i, j: : 0 <= i < j < a.Length ==> a[i] <= a[j]
    ensures multiset(a[..]) == old(multiset(a[..])) -> bool {
    
}
spec fn SwapFrame(a: Vec<int>, lo: int, hi: int)
    requires 0 <= lo <= hi <= a.Length
    reads a
{
}


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

spec fn spec_SelectionSort(a: Vec<int>, j: : 0 <= i < j < a.Length ==> a[i] <= a[j]
    ensures multiset(a[..]) == old(multiset(a[..]))
{
}


// SPEC 

method QuickSort(a: array<int>)
    modifies a
    ensures forall i, j: : 0 <= i < j < a.Length ==> a[i] <= a[j]
    ensures multiset(a[..]) == old(multiset(a[..]))
{
}

twostate predicate SwapFrame(a: array<int>, lo: int, hi: int)
    requires 0 <= lo <= hi <= a.Length
    reads a
{
}


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
    ensures SplitPoint(a, lo) && SplitPoint(a, hi)
{
}


// SPEC 

method Partition(a: Vec<int>, lo: int, hi: int) -> p: int
    requires
        0 <= lo <= hi <= a.len()
    reads a,
        0 <= lo <= hi <= a.len()
    reads a,
        0 <= lo <= hi <= a.len(),
        SplitPoint(a, lo) && SplitPoint(a, hi)
    modifies a,
        0 <= lo < hi <= a.len(),
        SplitPoint(a, lo) && SplitPoint(a, hi)
    modifies a
    ensures
        forall |i: int, j: int| 0 <= i < j < a.len() ==> a.index(i) <= a.index(j),
        multiset(a.index(..)) == old(multiset(a.index(..))),
        forall |i: int, j: int| 0 <= i < j < a.len() ==> a.index(i) <= a.index(j),
        multiset(a.index(..)) == old(multiset(a.index(..))),
        forall |i: int, j: int| lo <= i < j < hi ==> a.index(i) <= a.index(j),
        SwapFrame(a, lo, hi),
        SplitPoint(a, lo) && SplitPoint(a, hi),
        lo <= p < hi,
        forall |i: int| lo <= i < p ==> a.index(i) < a.index(p),
        forall |i: int| p <= i < hi ==> a.index(p) <= a.index(i),
        SplitPoint(a, lo) && SplitPoint(a, hi),
        SwapFrame(a, lo, hi)
;

proof fn lemma_SelectionSort(a: Vec<int>, j: : 0 <= i < j < a.Length ==> a[i] <= a[j]
    ensures multiset(a[..]) == old(multiset(a[..]))
{
}


// SPEC 

method QuickSort(a: array<int>)
    modifies a
    ensures forall i, j: : 0 <= i < j < a.Length ==> a[i] <= a[j]
    ensures multiset(a[..]) == old(multiset(a[..]))
{
}

twostate predicate SwapFrame(a: array<int>, lo: int, hi: int)
    requires 0 <= lo <= hi <= a.Length
    reads a
{
}


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
    ensures SplitPoint(a, lo) && SplitPoint(a, hi)
{
}


// SPEC 

method Partition(a: Vec<int>, lo: int, hi: int) -> (p: int)
    requires
        0 <= lo <= hi <= a.len()
    reads a,
        0 <= lo <= hi <= a.len()
    reads a,
        0 <= lo <= hi <= a.len(),
        SplitPoint(a, lo) && SplitPoint(a, hi)
    modifies a,
        0 <= lo < hi <= a.len(),
        SplitPoint(a, lo) && SplitPoint(a, hi)
    modifies a
    ensures
        forall |i: int, j: int| 0 <= i < j < a.len() ==> a.index(i) <= a.index(j),
        multiset(a.index(..)) == old(multiset(a.index(..))),
        forall |i: int, j: int| 0 <= i < j < a.len() ==> a.index(i) <= a.index(j),
        multiset(a.index(..)) == old(multiset(a.index(..))),
        forall |i: int, j: int| lo <= i < j < hi ==> a.index(i) <= a.index(j),
        SwapFrame(a, lo, hi),
        SplitPoint(a, lo) && SplitPoint(a, hi),
        lo <= p < hi,
        forall |i: int| lo <= i < p ==> a.index(i) < a.index(p),
        forall |i: int| p <= i < hi ==> a.index(p) <= a.index(i),
        SplitPoint(a, lo) && SplitPoint(a, hi),
        SwapFrame(a, lo, hi)
{
    0
}

}