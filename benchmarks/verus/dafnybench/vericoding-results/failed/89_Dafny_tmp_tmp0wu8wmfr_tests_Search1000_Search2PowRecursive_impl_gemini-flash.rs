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
proof fn lemma_div2_2pow(n: int)
    requires is_2_pow(n)
    ensures is_2_pow(n/2)
    decreases n
{
    match n {
        1 => {
            assert(1/2 == 0); // specific case for 1: 1/2 is 0 or 1 depending on int division. is_2_pow for 0 is false, not applicable
        }
        _ => {
            if n > 1 {
                // n % 2 == 0 && is_2_pow(n / 2) is true from is_2_pow(n)
                // then is_2_pow(n/2) is also true
                lemma_div2_2pow(n / 2);
            }
        }
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
    match n {
        0 => {
            k
        }
        _ => {
            let m: usize = i + (n / 2);
            assert((n + 1) / 2 == n / 2 + 1); // for (n+1) to be a power of 2, n must be of the form 2^k-1.
                                              // this means n is odd. (n+1)/2 vs n/2 depends on int division.
                                              // Here (n+1) is 2^k, then (n+1)/2 is 2^(k-1).
                                              // n is odd, so n/2 is (n-1)/2. (n+1)/2 is (n+1)/2.
                                              // (n / 2) + 1 is (n-1)/2 + 1 = (n+1)/2
            assert(is_2_pow((n + 1) as int));
            lemma_div2_2pow((n + 1) as int); // Now we know is_2_pow((n+1)/2)
            assert(is_2_pow(((n / 2) + 1) as int)); // because (n+1)/2 = n/2 + 1

            if a[m] < x {
                // If a[m] < x, then x must be in the right half (m+1..i+n-1) or not present.
                // The new segment starts at m+1, has length n/2.
                // The crucial part is that (n/2 + 1) is also a power of 2
                // because (n+1) is a power of 2, so (n+1)/2 is a power of 2, and (n+1)/2 = (n/2) + 1.
                // So, the recursive call `search_2_pow_recursive(a, m + 1, n / 2, x)` maintains the `is_2_pow` precondition.
                search_2_pow_recursive(a, m + 1, n / 2, x)
            } else if a[m] > x {
                // If a[m] > x, then x must be in the left half (i..m-1) or not present.
                // The new segment starts at i, has length n/2.
                // Property (n/2 + 1) being a power of 2 is preserved for the recursive call.
                search_2_pow_recursive(a, i, n / 2, x)
            } else { // a[m] == x
                // If a[m] == x, then m is the correct index for k.
                m
            }
        }
    }
}
// </vc-code>

fn main() {}

}