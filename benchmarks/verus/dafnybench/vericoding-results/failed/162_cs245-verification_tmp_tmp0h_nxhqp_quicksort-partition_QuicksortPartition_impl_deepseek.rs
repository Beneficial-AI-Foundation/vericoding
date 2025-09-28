use vstd::prelude::*;

verus! {

// Quicksort Partition -- Stephanie McIntyre
// Based on examples in class 
// Parts have been modified cause you know, arrays are different...

/* The annotations and implied proofs are left for you.
   I might do them later on next week. */

// <vc-helpers>
spec fn less_than_or_equal_to(seq: Seq<i32>, p: i32, start: int, end: int) -> bool {
    forall|i: int| start <= i < end ==> seq[i] <= p
}

spec fn greater_than(seq: Seq<i32>, p: i32, start: int, end: int) -> bool {
    forall|i: int| start <= i < end ==> seq[i] > p
}

proof fn lemma_swap_preserves_multiset<T>(seq: &mut Vec<T>, i: usize, j: usize)
    requires
        old(seq).len() >= 1,
        i < old(seq).len(),
        j < old(seq).len(),
    ensures
        seq@.to_multiset() == old(seq)@.to_multiset(),
{
}

proof fn lemma_swap_preserves_multiset_range<T>(seq: &mut Vec<T>, i: usize, j: usize, start: int, end: int)
    requires
        old(seq).len() >= 1,
        i < old(seq).len(),
        j < old(seq).len(),
        0 <= start <= end <= old(seq).len() as int,
        i as int >= start,
        i as int < end,
        j as int >= start,
        j as int < end,
    ensures
        seq@.subrange(start, end).to_multiset() == old(seq)@.subrange(start, end).to_multiset(),
{
}

spec fn multiset_unchanged_except_swap<T>(seq1: Seq<T>, seq2: Seq<T>, i: usize, j: usize) -> bool {
    seq1.to_multiset() == seq2.to_multiset()
}
// </vc-helpers>

// <vc-spec>
fn quicksort_partition(x: &mut Vec<i32>, n: usize, p: i32) -> (result: (usize, usize))
/*Pre-Condition*/   requires old(x).len() >= 1, n == old(x).len();
/*Post-Condition*/  ensures result.1 >= n;
                    ensures forall|i: int| 0 <= i < (result.0 as int) && (result.0 as int) < (n as int) ==> x[i] <= p;
                    ensures result.0 == n || (forall|i: int| (result.0 as int) <= i && i < (n as int) ==> x[i] > p);
                    ensures x@.to_multiset() == old(x)@.to_multiset()           //This says the new X is a permutation of our old version of X.
// </vc-spec>
// <vc-code>
{
    let mut lo: usize = 0;
    let mut mid: usize = 0;
    let mut hi: usize = n;
    
    assert(x@.to_multiset() == old(x)@.to_multiset());
    
    while mid < hi
        invariant
            hi <= n,
            lo <= mid <= hi,
            less_than_or_equal_to(x@, p, 0, lo as int),
            less_than_or_equal_to(x@, p, lo as int, mid as int),
            greater_than(x@, p, hi as int, n as int),
            x@.to_multiset() == old(x)@.to_multiset(),
    {
        let current = x[mid];
        
        if current <= p {
            if current < p {
                proof {
                    lemma_swap_preserves_multiset(x, lo, mid);
                }
                x.swap(lo, mid);
                
                assert(x@.to_multiset() == old(x)@.to_multiset());
            }
            lo = lo + 1;
            mid = mid + 1;
        } else {
            proof {
                lemma_swap_preserves_multiset(x, hi - 1, mid);
            }
            x.swap(hi - 1, mid);
            hi = hi - 1;
            
            assert(x@.to_multiset() == old(x)@.to_multiset());
        }
    }
    
    assert(lo <= hi);
    assert(hi <= n);
    assert(less_than_or_equal_to(x@, p, 0, lo as int));
    
    (lo, hi)
}
// </vc-code>

fn main() {
}

}