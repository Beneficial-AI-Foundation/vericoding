use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn Sorted(q: Seq<int>) -> bool {
    forall i,j :: 0 <= i <= j < q.len() ==> q.spec_index(i) <= q.spec_index(j)
}
spec fn HasAddends(q: Seq<int>, x: int) -> bool {
    exists i,j :: 0 <= i < j < q.len() && q.spec_index(i) + q.spec_index(j) == x
}

fn FindAddends(q: Seq<int>, x: int) -> (i: nat, j: nat)
    requires
        Sorted(q) && HasAddends(q, x)
    ensures
        i < j < q.len() && q.spec_index(i)+q.spec_index(j) == x
{
    let mut i: usize = 0;
    while i < q.len()
        invariant
            0 <= i <= q.len(),
            HasAddends(q, x),
            Sorted(q),
            forall k1, k2 :: 0 <= k1 < i && k1 < k2 < q.len() ==> q.spec_index(k1) + q.spec_index(k2) != x
    {
        let mut j: usize = i + 1;
        while j < q.len()
            invariant
                0 <= i < j <= q.len(),
                HasAddends(q, x),
                Sorted(q),
                forall k1, k2 :: 0 <= k1 < i && k1 < k2 < q.len() ==> q.spec_index(k1) + q.spec_index(k2) != x,
                forall k2 :: i < k2 < j ==> q.spec_index(i) + q.spec_index(k2) != x
        {
            if q.spec_index(i) + q.spec_index(j) == x {
                return (i, j);
            }
            j = j + 1;
        }
        i = i + 1;
    }
    
    // This point should never be reached due to the precondition HasAddends(q, x)
    // But we need to return something to satisfy the compiler
    assert(false);
    return (0, 1);
}

}