use vstd::prelude::*;

verus! {

// Author: Snorri Agnarsson, snorri@hi.is

// Search1000 is a Dafny version of a function shown
// by Jon Bentley in his old Programming Pearls
// column in CACM.  Surprisingly Dafny needs no help
// to verify the function.

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

// This method is a binary search that only works for array
// segments of size n == 2^k-1 for some k>=0.

// <vc-helpers>
#[verifier::proof]
fn lemma_sub_pow(n: int)
    requires
        n >= 1,
        is_2_pow(n),
    ensures
        is_2_pow(n / 2 + 1),
        is_2_pow(n - n / 2),
{
    if n == 1 {
        assert(n / 2 + 1 == 1);
        assert(n - n / 2 == 1);
    } else {
        assert(n % 2 == 0);
        assert(is_2_pow(n / 2));
        assert(is_2_pow(n / 2 + 1));
        assert(is_2_pow(n - n / 2));
    }
}
// </vc-helpers>

// <vc-spec>
fn search_2_pow_recursive(a: &[i32], i: usize, n: usize, x: i32) -> (k: usize)
    decreases n
    requires
        i + n <= a.len(),
        forall|p: int, q: int| 
            0 <= p < q && i as int <= p && q < (i + n) as int ==> 
            a[p] <= a[q],
        is_2_pow((n + 1) as int),
    ensures
        i <= k <= i + n,
        forall|r: int| 
            0 <= r && i as int <= r < k as int ==> 
            a[r] < x,
        forall|r: int| 
            0 <= r && k as int <= r < (i + n) as int ==> 
            a[r] >= x,
// </vc-spec>
// <vc-code>
{
    if n == 0 {
        i
    } else {
        let m = n / 2;
        let mid = i + m;
        if x <= a@[mid as int] {
            proof {
                lemma_sub_pow((n + 1) as int);
                assert(is_2_pow((m + 1) as int));
                assert(((i as int) + (m as int)) < ((a.len() as int)));
            }
            let left_k = search_2_pow_recursive(a, i, m, x);
            proof {
                assert(i <= left_k <= i + m);
                assert(x <= a@[mid as int]);
                assert(forall|r: int| 0 <= r && (i as int) <= r < (left_k as int) ==> a@[r] < x);
                assert(forall|r: int| 0 <= r && (left_k as int) <= r < ((i + m) as int) ==> a@[r] >= x);
                assert(forall|r: int| 0 <= r && ((i + m) as int) <= r < ((i + n) as int) ==> a@[r] >= a@[mid as int] >= x);
            }
            left_k
        } else {
            proof {
                lemma_sub_pow((n + 1) as int);
                assert(is_2_pow((n - m) as int));
                assert((((mid + 1) as int) + ((n - m - 1) as int)) <= ((a.len() as int)));
            }
            let right_k = search_2_pow_recursive(a, mid + 1, n - m - 1, x);
            proof {
                assert(mid + 1 <= right_k <= i + n);
                assert(a@[mid as int] < x);
                assert(forall|r: int| 0 <= r && (i as int) <= r <= (mid as int) ==> a@[r] <= a@[mid as int] < x);
                assert(forall|r: int| 0 <= r && ((mid + 1) as int) <= r < (right_k as int) ==> a@[r] < x);
                assert(forall|r: int| 0 <= r && (right_k as int) <= r < ((i + n) as int) ==> a@[r] >= x);
            }
            right_k
        }
    }
}
// </vc-code>

fn main() {}

}