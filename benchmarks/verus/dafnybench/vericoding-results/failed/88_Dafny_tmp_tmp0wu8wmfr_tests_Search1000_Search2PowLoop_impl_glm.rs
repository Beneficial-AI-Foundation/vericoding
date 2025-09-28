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
proof fn lemma_2_pow_decreases(n: int)
    requires
        is_2_pow(n)
    decreases n
{
    if n > 1 {
        assert(n % 2 == 0);
        lemma_2_pow_decreases(n / 2);
    }
}

proof fn lemma_mid_in_bounds(l: usize, r: usize)
    requires
        l < r,
    ensures
        l <= l + (r - l) / 2 < r,
{
    assert((r - l) > 0);
    assert((r - l) / 2 >= 0);
    assert(l + (r - l) / 2 >= l);
    assert((r - l) % 2 == 0 || (r - l) % 2 == 1);
    if (r - l) % 2 == 0 {
        assert(l + (r - l) / 2 < l + (r - l));
    } else {
        assert(l + (r - l) / 2 + 1 <= l + (r - l));
    }
}
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
    let mut l = i;
    let mut r = i + n;

    while l < r
        invariant
            i <= l <= r <= i + n,
            forall|p: int| i <= p < l ==> a@[p] < x,
            forall|p: int| r <= p < i + n ==> a@[p] >= x,
        decreases r - l,
    {
        lemma_mid_in_bounds(l, r);
        let mid = l + (r - l) / 2;
        assert(mid < r);
        assert(r <= i + n);
        assert(i + n <= a.len());
        assert(mid < a.len());
        if a[mid] < x {
            l = mid + 1;
            proof {
                assert forall|p: int| i <= p < l ==> a@[p] < x
                by {
                    if i <= p < mid {
                        assert(a@[p] < x);
                    } else if p == mid {
                        assert(a@[mid] < x);
                    }
                }
            }
        } else {
            r = mid;
            proof {
                assert forall|p: int| r <= p < i + n ==> a@[p] >= x
                by {
                    assert(r == mid);
                    if mid <= p < i + n {
                        assert(a@[p] >= x);
                    }
                }
            }
        }
    }
    l
}
// </vc-code>

// This method is a binary search that only works for array
// segments of size n == 2^k-1 for some k>=0.

fn main() {}

}