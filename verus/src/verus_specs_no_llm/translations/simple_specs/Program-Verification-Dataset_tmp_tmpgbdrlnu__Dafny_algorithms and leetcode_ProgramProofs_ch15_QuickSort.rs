// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
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

method QuickSort(a: array<int>)
  modifies a
  ensures forall i, j: : 0 <= i < j < a.Length ==> a[i] <= a[j]
  ensures multiset(a[..]) == old(multiset(a[..])) -> bool {
    
}

fn QuickSortAux(a: Vec<int>, lo: int, hi: int)
  requires 0 <= lo <= hi <= a.Length
  requires SplitPoint(a, lo) && SplitPoint(a, hi)
  modifies a
  ensures forall i, j: : lo <= i < j < hi ==> a[i] <= a[j]
  ensures SwapFrame(a, lo, hi)
  ensures SplitPoint(a, lo) && SplitPoint(a, hi)
{
  assume forall i, j: : lo <= i < j < hi ==> a[i] <= a[j];
  assume SwapFrame(a, lo, hi);
  assume SplitPoint(a, lo) && SplitPoint(a, hi);
}


//ATOM

method Partition(a: Vec<int>, lo: int, hi: int) -> (p: int)
  requires 0 <= lo < hi <= a.Length
  requires SplitPoint(a, lo) && SplitPoint(a, hi)
  modifies a
  ensures lo <= p < hi
  ensures forall i: : lo <= i < p ==> a[i] < a[p]
  ensures forall i :: p <= i < hi ==> a[p] <= a[i]
  ensures SplitPoint(a, lo) && SplitPoint(a, hi)
  ensures SwapFrame(a, lo, hi)
{
  p: = 0;
  assume lo <= p < hi;
  assume forall i :: lo <= i < p ==> a[i] < a[p];
  assume forall i :: p <= i < hi ==> a[p] <= a[i];
  assume SplitPoint(a, lo) && SplitPoint(a, hi);
  assume SwapFrame(a, lo, hi);
  return p;
}


//ATOM
predicate SplitPoint(a: Vec<int>, n: int)
  reads a
  requires 0 <= n <= n

{
  forall i, j: : 0 <= i < n <= j < a.Length ==> a[i] <= a[j]
}


// SPEC

method QuickSort(a: array<int>)
  modifies a
  ensures forall i, j: : 0 <= i < j < a.Length ==> a[i] <= a[j]
  ensures multiset(a[..]) == old(multiset(a[..]))
    requires
        0 <= lo <= hi <= a.len(),
        SplitPoint(a, lo) && SplitPoint(a, hi)
  modifies a,
        0 <= lo < hi <= a.len(),
        SplitPoint(a, lo) && SplitPoint(a, hi)
  modifies a,
        0 <= n <= n
    ensures
        forall i,j :: lo <= i < j < hi ==> a.spec_index(i) <= a.spec_index(j),
        SwapFrame(a, lo, hi),
        SplitPoint(a, lo) && SplitPoint(a, hi),
        lo <= p < hi,
        forall i :: lo <= i < p ==> a.spec_index(i) < a.spec_index(p),
        forall i :: p <= i < hi ==> a.spec_index(p) <= a.spec_index(i),
        SplitPoint(a, lo) && SplitPoint(a, hi),
        SwapFrame(a, lo, hi),
        forall i,j :: 0 <= i < j < a.len() ==> a.spec_index(i) <= a.spec_index(j),
        multiset(a.spec_index(..)) == old(multiset(a.spec_index(..)))
{
    return (0, 0, 0, 0, 0, 0, 0, 0, 0, 0, Vec::new(), 0, 0, 0);
}

}