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
fn quicksort_partition(x: &mut Vec<i32>, n: usize, p: i32) -> (result: (usize, usize))
/*Pre-Condition*/   requires old(x).len() >= 1, n == old(x).len();
/*Post-Condition*/  ensures result.1 >= n;
                    ensures forall|i: int| 0 <= i < (result.0 as int) && (result.0 as int) < (n as int) ==> x[i] <= p;
                    ensures result.0 == n || (forall|i: int| (result.0 as int) <= i && i < (n as int) ==> x[i] > p);
                    ensures x@.to_multiset() == old(x)@.to_multiset()           //This says the new X is a permutation of our old version of X.
// </vc-spec>
// <vc-code>
{
  // Begin function body implementation
  proof {
    use_type_invariant::<Vec<i32>>();
  }
  let ghost initial = x@;
  let mut i: usize = 0;
  for j: usize in 0..n
    invariant
      0 <= i <= j <= n,
      forall|k: int| 0 <= k < (i as int) ==> x@[k] <= p,
      forall|k: int| (i as int) <= k < (j as int) ==> x@[k] > p,
      x@.to_multiset() == initial@.to_multiset(),
  {
    if x[j] <= p {
      x.swap(i, j);
      proof {
        assert(old(x)@.to_multiset() == x@.to_multiset());
      }
      i += 1;
    }
  }
  let result = (i, n);
  result
}
// </vc-code>
// </vc-code>

fn main() {
}

}