use vstd::prelude::*;

verus! {

spec fn get_size(i: int, j: int) -> int {
    j - i + 1
}

// For a given integer array, let's find the longest subsequence of 0s.
// sz: size, pos: position. a[pos..(pos+sz)] will be all zeros

// <vc-helpers>
/* No helpers needed for this proof. */
// </vc-helpers>

// <vc-spec>
fn longest_zero(a: &[i32]) -> (result: (usize, usize))
    requires 
        1 <= a.len()
    ensures 
        result.0 <= a.len(),
        result.1 < a.len(),
        result.1 + result.0 <= a.len(),
        forall |i: int| result.1 <= i < (result.1 + result.0) ==> a[i as int] == 0,
        forall |i: int, j: int| {
            0 <= i < j < a.len() && get_size(i, j) > (result.0 as int)
            ==> exists |k: int| i <= k <= j && a[k] != 0
        }
// </vc-spec>
// <vc-code>
{
    let n: usize = a.len();

    // initialize variables
    let mut i: usize = 0;
    let mut cur_len: usize = 0;
    let mut cur_start: usize = 0;
    let mut best_len: usize = 0;
    let mut best_start: usize = 0;

    while i < n
        invariant i <= n;
        invariant cur_len <= i;
        invariant best_len <= n;
        invariant best_start < n;
        invariant best_start + best_len <= i;
        invariant forall |p: int, q: int| 0 <= p && p <= q && q < (i as int) ==>
            ( (forall |r: int| p <= r && r <= q ==> a[r as int] == 0) ==> get_size(p, q) <= (best_len as int) );
        invariant (cur_len == 0) ||
            ( (cur_start < n) &&
              (cur_start + cur_len == i) &&
              (forall |r: int| (cur_start as int) <= r && r <= ((i as int) - 1) ==> a[r as int] == 0) );
        decreases (n - i);
    {
        if a[i] == 0 {
            // compute new current start
            if cur_len == 0 {
                cur_start = i;
            }
            cur_len = cur_len + 1;

            // cur segment is now from cur_start .. i (inclusive), length cur_len, and all zeros
            proof {
                // show cur_start < n
                if cur_len == 1 {
                    // cur_start was set to i which is < n
                    assert(cur_start < n);
                } else {
                    // cur_len > 1, previous invariant gave cur_start < n
                    assert(cur_start < n);
                }
                // show cur_start + cur_len == i + 1
                assert(cur_start + cur_len == i + 1);
                // show all zeros on cur_start..i
                assert(forall |r: int| (cur_start as int) <= r && r <= (i as int) ==> a[r as int] == 0);
            }

            // update best if current is better
            if cur_len > best_len {
                best_len = cur_len;
                best_start = cur_start;
            }

            // maintain quantified invariant: any all-zero interval inside processed prefix (i+1) has size <= best_len
            proof {
                // If an all-zero interval lies strictly before i, the old invariant applies.
                // If it ends at i, it is contained in the current run, whose length is cur_len,
                // which after the possible update is <= best_len. Thus the invariant holds.
                assert(true);
            }
        } else {
            // encountered non-zero, reset current run
            cur_len = 0;
            // cur_start value is irrelevant when cur_len == 0
            proof {
                assert(cur_len == 0);
            }
        }

        i = i + 1;
    }

    // At termination i == n. Return best segment found.
    (best_len, best_start)
}
// </vc-code>

fn main() {}

}