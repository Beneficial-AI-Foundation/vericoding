// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn sorted_seq(a: Seq<int>) -> bool {
    forall i, j :: 0 <= i <= j < a.len() ==> a.spec_index(i) <= a.spec_index(j)
}
spec fn sorted_slice(a: Vec<int>, start: int, end: int)
 requires 0 <= start <= end <= a.Length
 reads a
{
 forall i, j: : start <= i <= j < end ==> a[i] <= a[j]
}


// SPEC
method mergeSimple(a1: seq<int>, a2: Seq<int>, start: int, end: int, b: Vec<int>, start, end) -> bool {
    
}

}