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
spec fn is_2_pow_minus_one(n: int) -> bool
    decreases n
{
    if n < 0 {
        false
    } else if n == 0 {
        true
    } else {
        (n + 1) % 2 == 0 && is_2_pow(n + 1)
    }
}

proof fn lemma_midpoint(low: int, high: int)
    requires
        low <= high,
    ensures
        low <= (low + high) / 2 <= high,
    decreases high - low
{
    if low == high {
    } else {
        lemma_midpoint(low + 1, high);
    }
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
fn search_1000(a: &[i32], x: i32) -> (k: usize)
    requires
        a.len() >= 1000,
        forall|p: int, q: int| 0 <= p < q < 1000 ==> a[p] <= a[q],
    ensures
        0 <= k <= 1000,
        forall|r: int| 0 <= r < k ==> a[r] < x,
        forall|r: int| k <= r < 1000 ==> a[r] >= x,
{
    let mut low: usize = 0;
    let mut high: usize = 1000;

    while low < high
        invariant
            0 <= low <= high <= 1000,
            forall|r: int| 0 <= r < low ==> a[r] < x,
            forall|r: int| high <= r < 1000 ==> a[r] >= x,
        decreases high - low
    {
        proof {
            lemma_midpoint(low as int, high as int);
        }
        let mid = (low + high) / 2;
        if a[mid] < x {
            low = mid + 1;
        } else {
            high = mid;
        }
    }
    low
}
// </vc-code>

fn main() {
}

}