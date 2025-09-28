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
proof fn lemma_2_pow_divide(n: nat)
    requires 
        n > 0,
        is_2_pow((n + 1) as int),
    ensures 
        n % 2 == 1,
        is_2_pow(((n / 2) + 1) as int),
    decreases n + 1
{
    // Since is_2_pow(n+1) and n+1 > 1, we have (n+1) % 2 == 0 and is_2_pow((n+1)/2)
    assert((n + 1) > 1);
    assert((n + 1) % 2 == 0);
    assert(is_2_pow(((n + 1) / 2) as int));
    
    // Since (n+1) is even, n must be odd
    assert(n % 2 == 1);
    
    // When n is odd, (n+1)/2 == (n/2) + 1
    assert(((n + 1) / 2) == ((n / 2) + 1));
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
        return i;
    }
    
    proof {
        lemma_2_pow_divide(n);
    }
    
    let mid = i + n / 2;
    
    if a[mid] < x {
        // Search in the right half
        let k = search_2_pow_recursive(a, mid + 1, n / 2, x);
        
        assert forall|r: int| 0 <= r && i as int <= r < mid as int
            implies a[r] < x by {
            assert(a[r] <= a[mid]);  // by sortedness
            assert(a[mid] < x);       // by condition
        }
        
        assert forall|r: int| 0 <= r && mid as int <= r <= mid as int
            implies a[r] < x by {
            assert(r == mid);
        }
        
        k
    } else {
        // Search in the left half
        let k = search_2_pow_recursive(a, i, n / 2, x);
        
        assert forall|r: int| 0 <= r && (mid + 1) as int <= r < (i + n) as int
            implies a[r] >= x by {
            assert(a[mid] <= a[r]);  // by sortedness
            assert(a[mid] >= x);      // by condition
        }
        
        assert forall|r: int| 0 <= r && mid as int <= r < (i + n) as int
            implies a[r] >= x by {
            if r == mid {
                assert(a[r] >= x);
            } else {
                assert(r >= (mid + 1) as int);
            }
        }
        
        k
    }
}
// </vc-code>

fn main() {}

}