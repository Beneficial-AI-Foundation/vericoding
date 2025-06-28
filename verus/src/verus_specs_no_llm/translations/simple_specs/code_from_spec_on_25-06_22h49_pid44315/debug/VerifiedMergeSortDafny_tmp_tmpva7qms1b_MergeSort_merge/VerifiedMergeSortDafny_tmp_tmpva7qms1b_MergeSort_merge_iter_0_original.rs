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


//ATOM


predicate merged(a1: seq<int>, a2: Seq<int>, b: Vec<int>, start: int, end: int)
 reads b
 requires end - start == |a2| + |a1|
 requires 0 <= start <= end <= b.Length
{
 multiset(a1) + multiset(a2) == multiset(b[start..end])
}


// SPEC

method merge(a1: seq<int>, a2: Seq<int>, start: int, end: int, b: Vec<int>, start, end)
 requires b.Length == |a2| + |a1|
 ensures merged(a1, a2, b, start, end) -> bool {
    
}

}