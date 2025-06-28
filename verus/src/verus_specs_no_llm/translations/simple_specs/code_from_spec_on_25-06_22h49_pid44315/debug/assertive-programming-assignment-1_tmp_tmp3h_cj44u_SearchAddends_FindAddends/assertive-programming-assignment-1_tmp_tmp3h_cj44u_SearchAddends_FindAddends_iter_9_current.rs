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
                forall |k2: int| (i as int) < k2 < j ==> q.spec_index(i as int) + q.spec_index(k2) != x
        {
            if q.spec_index(i as int) + q.spec_index(j as int) == x {
                return (i as nat, j as nat);
            }
            j = j + 1;
        }
        i = i + 1;
    }
    
    // This point should be unreachable due to the precondition
    proof {
        // We have i == q.len() at this point
        assert(i == q.len());
        
        // From HasAddends(q, x), there exists a pair that sums to x
        assert(HasAddends(q, x));
        
        // The loop invariant tells us no pair with first element < i sums to x  
        assert(forall |k1: int, k2: int| 0 <= k1 < (i as int) && k1 < k2 < q.len() ==> q.spec_index(k1) + q.spec_index(k2) != x);
        
        // Since i == q.len(), for any valid pair 0 <= k1 < k2 < q.len(), we have k1 < i
        assert(forall |k1: int, k2: int| 0 <= k1 < k2 < q.len() ==> k1 < (i as int));
        
        // Therefore no valid pair can sum to x, contradicting HasAddends
        assert(forall |k1: int, k2: int| 0 <= k1 < k2 < q.len() ==> q.spec_index(k1) + q.spec_index(k2) != x);
        
        // This directly contradicts HasAddends(q, x)
        assert(false) by {
            // HasAddends(q, x) means there exists some pair that sums to x
            // But we just proved no such pair exists
            assert(exists |i: int, j: int| 0 <= i < j < q.len() && q.spec_index(i) + q.spec_index(j) == x);
            assert(forall |i: int, j: int| 0 <= i < j < q.len() ==> q.spec_index(i) + q.spec_index(j) != x);
        }
    }
    
    // This is unreachable, but we need to return something to satisfy the type checker
    (0, 1)
}

}