use vstd::prelude::*;

verus! {

// Author: Snorri Agnarsson, snorri@hi.is

// Search1000 is a Verus version of a function shown
// by Jon Bentley in his old Programming Pearls
// column in CACM.  Surprisingly Verus needs no help
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
fn search_range_helper(a: &[i32], x: i32, lo: usize, hi: usize) -> (k: usize)
    requires
        a.len() >= 1000usize,
        lo <= hi && hi <= 1000usize,
        forall|p: int, q: int| 0 <= p < q < 1000 ==> a@[p] <= a@[q],
    ensures
        lo <= k && k <= hi,
        forall|r: int| lo as int <= r && r < k as int ==> a@[r] < x,
        forall|r: int| k as int <= r && r < hi as int ==> a@[r] >= x,
    decreases (hi as int - lo as int)
{
    if lo == hi {
        lo
    } else {
        let mid: usize = (lo + hi) / 2;
        if a[mid] < x {
            search_range_helper(a, x, mid + 1, hi)
        } else {
            search_range_helper(a, x, lo, mid)
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn search_1000(a: &[i32], x: i32) -> (k: usize)
    requires 
        a.len() >= 1000,
        forall|p: int, q: int| 0 <= p < q < 1000 ==> a[p] <= a[q],
    ensures 
        0 <= k <= 1000,
        forall|r: int| 0 <= r < k ==> a[r] < x,
        forall|r: int| k <= r < 1000 ==> a[r] >= x,
// </vc-spec>
// <vc-code>
{
    search_range_helper(a, x, 0usize, 1000usize)
}
// </vc-code>

fn main() {
}

}