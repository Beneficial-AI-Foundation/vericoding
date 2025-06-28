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
    
    // At this point, we've checked all pairs (k1, k2) with 0 <= k1 < k2 < q.len()
    // and found that none sum to x. But HasAddends(q, x) guarantees such a pair exists.
    // This is a contradiction, so this point is unreachable.
    
    // The key insight: when i reaches q.len(), the outer loop invariant tells us that
    // for all k1 < i (i.e., k1 < q.len()) and k1 < k2 < q.len(), we have
    // q.spec_index(k1) + q.spec_index(k2) != x
    // This means we've checked all valid pairs and found none, contradicting HasAddends(q, x)
    
    proof {
        assert(i == q.len());
        assert(forall |k1: int, k2: int| 0 <= k1 < q.len() && k1 < k2 < q.len() ==> q.spec_index(k1) + q.spec_index(k2) != x);
        assert(HasAddends(q, x));
        assert(exists |i0: int, j0: int| 0 <= i0 < j0 < q.len() && q.spec_index(i0) + q.spec_index(j0) == x);
        // The above two assertions contradict each other
        assert(false);
    }
    
    (0, 1) // unreachable
}

}