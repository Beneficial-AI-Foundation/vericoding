use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn Sorted(q: Seq<int>) -> bool {
    forall |i: int, j: int| 0 <= i <= j < q.len() ==> q.spec_index(i) <= q.spec_index(j)
}

spec fn HasAddends(q: Seq<int>, x: int) -> bool {
    exists |i: int, j: int| 0 <= i < j < q.len() && q.spec_index(i) + q.spec_index(j) == x
}

fn FindAddends(q: Seq<int>, x: int) -> (i: nat, j: nat)
    requires
        Sorted(q) && HasAddends(q, x)
    ensures
        i < j < q.len() && q.spec_index(i as int) + q.spec_index(j as int) == x
{
    let mut i: usize = 0;
    while i < q.len()
        invariant
            0 <= i <= q.len(),
            HasAddends(q, x),
            Sorted(q),
            forall |k1: int, k2: int| 0 <= k1 < i && k1 < k2 < q.len() ==> q.spec_index(k1) + q.spec_index(k2) != x
    {
        let mut j: usize = i + 1;
        while j < q.len()
            invariant
                0 <= i < j <= q.len(),
                HasAddends(q, x),
                Sorted(q),
                forall |k1: int, k2: int| 0 <= k1 < i && k1 < k2 < q.len() ==> q.spec_index(k1) + q.spec_index(k2) != x,
                forall |k2: int| i < k2 < j ==> q.spec_index(i as int) + q.spec_index(k2) != x
        {
            if q.spec_index(i as int) + q.spec_index(j as int) == x {
                return (i as nat, j as nat);
            }
            j = j + 1;
        }
        i = i + 1;
    }
    
    // Prove that this point is unreachable
    // Since HasAddends(q, x) is true, there exist indices i0, j0 such that
    // q.spec_index(i0) + q.spec_index(j0) == x with 0 <= i0 < j0 < q.len()
    // Our loops exhaustively check all such pairs, so we must have found them
    assert(exists |i0: int, j0: int| 0 <= i0 < j0 < q.len() && q.spec_index(i0) + q.spec_index(j0) == x);
    assert(forall |k1: int, k2: int| 0 <= k1 < q.len() && k1 < k2 < q.len() ==> q.spec_index(k1) + q.spec_index(k2) != x);
    assert(false);
    (0, 1)
}

}