use vstd::prelude::*;

verus! {

// Quicksort Partition -- Stephanie McIntyre
// Based on examples in class 
// Parts have been modified cause you know, arrays are different...

/* The annotations and implied proofs are left for you.
   I might do them later on next week. */

// <vc-helpers>
// Helper lemma to prove that swapping preserves multiset
proof fn swap_preserves_multiset(s: Seq<i32>, i: int, j: int)
    requires
        0 <= i < s.len(),
        0 <= j < s.len(),
    ensures
        s.update(i, s[j]).update(j, s[i]).to_multiset() == s.to_multiset()
{
    assert(s.update(i, s[j]).update(j, s[i]) =~= s.update(i, s[j]).update(j, s[i]));
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
    let mut i: usize = 0;
    let mut j: usize = n;
    
    while i < j
        invariant
            i <= j,
            j <= n,
            n == x.len(),
            forall|k: int| 0 <= k < i ==> x@[k] <= p,
            forall|k: int| j <= k < n ==> x@[k] > p,
            x@.to_multiset() == old(x)@.to_multiset(),
    {
        if x[i] <= p {
            i = i + 1;
        } else {
            j = j - 1;
            if j < n && j < x.len() && x[j] <= p {
                // Swap x[i] and x[j]
                let temp = x[i];
                let old_x = x@;
                x.set(i, x[j]);
                proof {
                    assert(x@ == old_x.update(i as int, old_x[j as int]));
                }
                let mid_x = x@;
                x.set(j, temp);
                proof {
                    assert(x@ == mid_x.update(j as int, temp));
                    assert(x@ == old_x.update(i as int, old_x[j as int]).update(j as int, old_x[i as int]));
                    swap_preserves_multiset(old_x, i as int, j as int);
                }
                i = i + 1;
            }
        }
    }
    
    // At this point i == j
    proof {
        assert(i == j);
        assert(j <= n);
        assert(forall|k: int| 0 <= k < i ==> x@[k] <= p);
        assert(forall|k: int| j <= k < n ==> x@[k] > p);
        assert(i == n || forall|k: int| i <= k < n ==> x@[k] > p);
    }
    
    (i, n)
}
// </vc-code>

fn main() {
}

}