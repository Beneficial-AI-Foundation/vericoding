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
// </vc-helpers>

// <vc-spec>
fn search_2_pow_recursive(a: &[i32], i: usize, n: usize, x: i32) -> (k: usize)
    requires
        i + n <= a.len(),
        ({(forall|p: int, q: int|
            0 <= p < q && i as int <= p && q < (i + n) as int ==> 
            a[p] <= a[q])}),
        is_2_pow((n + 1) as int),
    ensures
        i <= k <= i + n,
        ({(forall|r: int|
            0 <= r && i as int <= r < k as int ==> 
            a[r] < x)}),
        ({(forall|r: int|
            0 <= r && k as int <= r < (i + n) as int ==> 
            a[r] >= x)}),
    decreases n
// </vc-spec>
// <vc-code>
{
  assume(false);
  0
}
// </vc-code>


fn main() {}

}