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
    
    // This point should be unreachable due to the contradiction
    proof {
        // At this point i == q.len()
        assert(i == q.len());
        
        // From HasAddends(q, x), we know there exists some pair that sums to x
        assert(HasAddends(q, x));
        
        // From the loop invariant, we know no pair (k1, k2) with k1 < i sums to x
        assert(forall |k1: int, k2: int| 0 <= k1 < i && k1 < k2 < q.len() ==> q.spec_index(k1) + q.spec_index(k2) != x);
        
        // Since i == q.len(), we have k1 < i equivalent to k1 < q.len()
        // For any valid pair 0 <= k1 < k2 < q.len(), we have k1 < q.len() = i
        assert(forall |k1: int, k2: int| 0 <= k1 < k2 < q.len() ==> k1 < i);
        
        // Therefore, no valid pair sums to x
        assert(forall |k1: int, k2: int| 0 <= k1 < k2 < q.len() ==> q.spec_index(k1) + q.spec_index(k2) != x);
        
        // This contradicts HasAddends(q, x)
        // We need to be more explicit about the contradiction
        let ghost witness_i: int, ghost witness_j: int = choose |i0: int, j0: int| 
            0 <= i0 < j0 < q.len() && q.spec_index(i0) + q.spec_index(j0) == x;
        
        // We have a witness pair that sums to x
        assert(0 <= witness_i < witness_j < q.len());
        assert(q.spec_index(witness_i) + q.spec_index(witness_j) == x);
        
        // But our invariant says no such pair exists
        assert(q.spec_index(witness_i) + q.spec_index(witness_j) != x);
        
        // This is the explicit contradiction
        assert(false);
    }
    
    // Since we proved false above, this is unreachable
    (0nat, 1nat)
}

}