// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn sorted_seq(a: Seq<int>) -> bool {
    forall |i: int, j: int| 0 <= i <= j < a.len() ==> a.index(i) <= a.index(j)
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