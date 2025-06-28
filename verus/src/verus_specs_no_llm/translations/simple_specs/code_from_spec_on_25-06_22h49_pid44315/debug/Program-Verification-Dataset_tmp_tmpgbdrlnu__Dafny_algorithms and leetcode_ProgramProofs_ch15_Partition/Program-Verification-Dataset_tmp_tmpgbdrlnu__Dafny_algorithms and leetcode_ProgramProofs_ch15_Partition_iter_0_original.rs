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


// SPEC

method Partition(a: array<int>, lo: int, hi: int) returns (p: int)
  requires 0 <= lo < hi <= a.Length
  requires SplitPoint(a, lo) && SplitPoint(a, hi)
  modifies a
  ensures lo <= p < hi
  ensures forall i: : lo <= i < p ==> a[i] < a[p]
  ensures forall i :: p <= i < hi ==> a[p] <= a[i]
  ensures SplitPoint(a, lo) && SplitPoint(a, hi)
  ensures SwapFrame(a, lo, hi) -> bool {
    
}

fn Partition(a: Vec<int>, lo: int, hi: int) -> (p: int)
    requires
        0 <= lo < hi <= a.len(),
        SplitPoint(a, lo) && SplitPoint(a, hi)
  modifies a
    ensures
        lo <= p < hi,
        forall i :: lo <= i < p ==> a.spec_index(i) < a.spec_index(p),
        forall i :: p <= i < hi ==> a.spec_index(p) <= a.spec_index(i),
        SplitPoint(a, lo) && SplitPoint(a, hi),
        SwapFrame(a, lo, hi)
{
    return 0;
}

}