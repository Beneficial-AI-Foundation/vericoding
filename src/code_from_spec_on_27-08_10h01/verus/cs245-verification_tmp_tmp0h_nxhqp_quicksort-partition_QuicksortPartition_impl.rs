use vstd::prelude::*;

verus! {

// Quicksort Partition -- Stephanie McIntyre
// Based on examples in class 
// Parts have been modified cause you know, arrays are different...

/* The annotations and implied proofs are left for you.
   I might do them later on next week. */

// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn quicksort_partition(x: &mut Vec<i32>, n: usize, p: i32) -> (result: (usize, usize))
/*Pre-Condition*/   requires old(x).len() >= 1, n == old(x).len();
/*Post-Condition*/  ensures result.1 >= n;
                    ensures forall|i: int| 0 <= i < (result.0 as int) && (result.0 as int) < (n as int) ==> x[i] <= p;
                    ensures result.0 == n || (forall|i: int| (result.0 as int) <= i && i < (n as int) ==> x[i] > p);
                    ensures x@.to_multiset() == old(x)@.to_multiset()           //This says the new X is a permutation of our old version of X.
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    let mut i = 0;
    let mut j = 0;
    
    while j < n
        invariant 
            0 <= i <= j <= n,
            x@.len() == n,
            forall|k: int| 0 <= k < i ==> x[k] <= p,
            forall|k: int| i <= k < j ==> x[k] > p,
            x@.to_multiset() == old(x)@.to_multiset()
    {
        if x[j] <= p {
            if i != j {
                let temp = x[i];
                x.set(i, x[j]);
                x.set(j, temp);
            }
            i = i + 1;
        }
        j = j + 1;
    }
    
    (i, n)
}
// </vc-code>

fn main() {
}

}