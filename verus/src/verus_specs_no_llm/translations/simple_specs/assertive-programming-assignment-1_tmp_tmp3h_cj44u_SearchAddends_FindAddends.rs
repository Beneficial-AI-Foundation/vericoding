// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn Sorted(q: Seq<int>) -> bool {
    forall |i: int, j: int| 0 <= i <= j < q.len() ==> q.index(i) <= q.index(j)
}
spec fn HasAddends(q: Seq<int>, x: int) -> bool {
    exists |i: int, j: int| 0 <= i < j < q.len() && q.index(i) + q.index(j) == x
}

spec fn spec_FindAddends(q: Seq<int>, x: int) -> i: nat, j: nat
    requires
        Sorted(q) && HasAddends(q, x)
    ensures
        i < j < q.len() && q.index(i)+q.index(j) == x
;

proof fn lemma_FindAddends(q: Seq<int>, x: int) -> (i: nat, j: nat)
    requires
        Sorted(q) && HasAddends(q, x)
    ensures
        i < j < q.len() && q.index(i)+q.index(j) == x
{
    (0, 0)
}

}