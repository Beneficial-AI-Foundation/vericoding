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
proof fn lemma_binary_search_invariant_preserved(
    a: &[i32], 
    x: i32, 
    left: usize, 
    right: usize, 
    mid: usize
)
    requires
        a.len() >= 1000,
        forall|p: int, q: int| 0 <= p < q < 1000 ==> a[p] <= a[q],
        left <= mid,
        mid < right,
        right <= 1000,
        forall|r: int| 0 <= r < left ==> a[r] < x,
        forall|r: int| right <= r < 1000 ==> a[r] >= x,
    ensures
        (a[mid] < x ==> (
            forall|r: int| 0 <= r < (mid + 1) as int ==> a[r] < x
        )) &&
        (a[mid] >= x ==> (
            forall|r: int| mid as int <= r < 1000 ==> a[r] >= x
        ))
{
}
// </vc-helpers>

// <vc-spec>
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
// </vc-spec>

// <vc-code>
{
    let mut left: usize = 0;
    let mut right: usize = 1000;
    
    while left < right
        invariant
            0 <= left <= right <= 1000,
            forall|r: int| 0 <= r < left ==> a[r] < x,
            forall|r: int| right <= r < 1000 ==> a[r] >= x,
        decreases right - left
    {
        let mid = left + (right - left) / 2;
        
        if a[mid] < x {
            proof {
                lemma_binary_search_invariant_preserved(a, x, left, right, mid);
            }
            left = mid + 1;
        } else {
            proof {
                lemma_binary_search_invariant_preserved(a, x, left, right, mid);
            }
            right = mid;
        }
    }
    
    left
}
// </vc-code>

fn main() {
}

}