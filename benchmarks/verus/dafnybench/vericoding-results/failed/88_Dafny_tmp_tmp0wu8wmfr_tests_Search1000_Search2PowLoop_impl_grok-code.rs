use vstd::prelude::*;

verus! {

// Author: Snorri Agnarsson, snorri@hi.is

// Search1000 is a Verus version of a function shown
// by Jon Bentley in his old Programming Pearls
// column in CACM.  

// Is2Pow(n) is true iff n==2^k for some k>=0.
spec fn is_2_pow(n: int) -> bool
    decreases n
{
    if n < 1 {
        false
    } else if n == 1 {
        true
    } else {
        n % 2 == 0 && is_2_pow(n / 2)
    }
}

// This method is a binary search that only works for array
// segments of size n == 2^k-1 for some k>=0.

// <vc-helpers>
// No additional helpers needed
// </vc-helpers>

// <vc-spec>
fn search_2_pow_loop(a: &[i32], i: usize, n: usize, x: i32) -> (k: usize)
    requires
        i <= i + n <= a.len(),
        forall|p: int, q: int| i <= p < q < (i + n) && 0 <= p < a.len() && 0 <= q < a.len() ==> 
            a@[p] <= a@[q],
        is_2_pow((n + 1) as int),
    ensures
        i <= k <= i + n,
        forall|r: int| i <= r < k && 0 <= r < a.len() ==> a@[r] < x,
        forall|r: int| k <= r < (i + n) && 0 <= r < a.len() ==> a@[r] >= x,
// </vc-spec>
// <vc-code>
{
    let mut left: usize = i;
    let mut right: usize = i + n;
    while left < right
    invariant
        i <= left <= right <= i + n,
        a@.len() >= right,
        forall |p: int| i <= p < (left as int) && 0 <= p < a@.len() ==> a@[p] < x,
        forall |q: int| (right as int) <= q < (i as int) + (n as int) && 0 <= q < a@.len() ==> a@[q] >= x,
        decreases (right as int) - (left as int)
    {
        let mid: usize = left + (right - left) / 2;
        proof {
            assert((mid as int) >= (left as int));
            assert((mid as int) < (right as int));
        }
        if a[mid] < x {
            proof {
                // Assert sorting: all in [left, mid) <= a[mid]
                assert(forall |p: int| #![trigger(a@[p], a@[mid as int])] (left as int) <= p < (mid as int) && 0 <= p < a@.len() && 0 <= (mid as int) < a@.len() ==> a@[p] <= a@[mid as int]);
                // Assert a[mid] <= x - 1 (since integer < implies <= -1)
                assert(a@[mid as int] <= (x as int) - 1);
                // Therefore, all in [left, mid+1) < x
                assert(forall |p: int| (left as int) <= p < (mid as int) + 1 && i <= p < a@.len() ==> a@[p] < x);
                // Now assert the invariant range for left: i <= p < mid
                assert(forall |p: int| (i as int) <= p < (mid as int) && 0 <= p < a@.len() ==> a@[p] < x);
            }
            left = mid + 1;
        } else {
            proof {
                // Assert a[mid] >= x
                assert(a@[mid as int] >= x);
 Blut                // Assert sorting: all in [mid, i+n) >= a[mid]
                assert(forall |q: int| #![trigger(a@[q], a@[mid as int])] (mid as int) <= q < (i as int) + (n as int) && 0 <= q < a@.len() && 0 <= (mid as int) < a@.len() ==> a@[q] >= a@[mid as int]);
                // Since a[mid] >= x, all in [mid, i+n) >= x
                // And assert the invariant range for right: right <= q < i+n (after setting, right = mid)
                assert(forall |q: int| (mid as int) <= q < (i as int) + (n as int) && 0 <= q < a@.len() ==> a@[q] >= x);
            }
            right = mid;
        }
    }
    proof {
        assert((left as int) == (right as int));
    }
    left
}
// </vc-code>

// This method is a binary search that only works for array
// segments of size n == 2^k-1 for some k>=0.

fn main() {}

}