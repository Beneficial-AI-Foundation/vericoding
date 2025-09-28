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
proof fn is_2_pow_properties(n: int)
    requires is_2_pow(n)
    ensures n >= 1
{
}

proof fn is_2_pow_div_2(n: int)
    requires is_2_pow(n), n > 1
    ensures is_2_pow(n / 2)
{
}

proof fn is_2_pow_minus_1_div_2(n: int)
    requires is_2_pow(n), n > 1
    ensures is_2_pow(((n - 1) / 2 + 1))
{
    assert(n % 2 == 0);
    assert(n / 2 >= 1);
    assert((n - 1) / 2 == n / 2 - 1);
    assert((n - 1) / 2 + 1 == n / 2);
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
    is_2_pow_properties((n + 1) as int);
    
    if n == 0 {
        return i;
    }
    
    let mid = i + n / 2;
    
    proof {
        is_2_pow_minus_1_div_2((n + 1) as int);
        assert(is_2_pow(((n + 1) as int - 1) / 2 + 1));
        assert(((n + 1) as int - 1) / 2 + 1 == (n / 2 + 1) as int);
        assert(is_2_pow((n / 2 + 1) as int));
    }
    
    if a[mid] < x {
        search_2_pow_recursive(a, mid + 1, n / 2, x)
    } else {
        search_2_pow_recursive(a, i, n / 2, x)
    }
}
// </vc-code>

fn main() {}

}