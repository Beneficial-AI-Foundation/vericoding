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
proof fn lemma_is_2_pow_div2(n: int)
    requires n > 1, is_2_pow(n)
    ensures is_2_pow(n / 2)
{
}

proof fn lemma_is_2_pow_positive(n: int)
    requires is_2_pow(n)
    ensures n >= 1
    decreases n
{
    if n < 1 {
    } else if n == 1 {
    } else {
        lemma_is_2_pow_positive(n / 2);
    }
}

proof fn lemma_is_2_pow_minus_one(n: int)
    requires is_2_pow(n), n > 1
    ensures is_2_pow((n - 1) / 2 + 1)
{
    assert((n - 1) / 2 + 1 == n / 2);
    lemma_is_2_pow_div2(n);
}

proof fn lemma_size_decreases(size: usize)
    requires size > 0, is_2_pow((size + 1) as int)
    ensures size / 2 < size
{
    lemma_is_2_pow_positive((size + 1) as int);
}

proof fn lemma_mid_bounds(low: usize, size: usize, high: usize, a_len: usize)
    requires low <= high, high - low == size, size > 0, low < a_len
    ensures low <= low + size / 2 < high, low + size / 2 < a_len
{
    assert(size > 0);
    assert(size / 2 < size);
    assert(low + size / 2 < low + size);
    assert(low + size == high);
}
// </vc-helpers>

// <vc-spec>
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
// </vc-spec>

// <vc-code>
{
    let mut low = i;
    let mut high = i + n;
    let mut size = n;
    
    while size > 0
        invariant
            i <= low <= high <= i + n,
            high - low == size,
            size <= n,
            is_2_pow((size + 1) as int),
            forall|r: int| i <= r < low && 0 <= r < a.len() ==> a@[r] < x,
            forall|r: int| high <= r < (i + n) && 0 <= r < a.len() ==> a@[r] >= x,
        decreases size
    {
        proof {
            lemma_is_2_pow_positive((size + 1) as int);
            lemma_mid_bounds(low, size, high, a.len());
        }
        
        let mid = low + size / 2;
        
        if a[mid] < x {
            let old_low = low;
            low = mid + 1;
            proof {
                assert(forall|r: int| i <= r < old_low && 0 <= r < a.len() ==> a@[r] < x);
                assert(a@[mid as int] < x);
                assert(mid as int >= old_low);
                assert(forall|r: int| i <= r < low && 0 <= r < a.len() ==> a@[r] < x);
            }
        } else {
            high = mid;
        }
        
        let old_size = size;
        size = size / 2;
        
        if size > 0 {
            proof {
                lemma_is_2_pow_minus_one((old_size + 1) as int);
            }
        }
    }
    
    low
}
// </vc-code>

// This method is a binary search that only works for array
// segments of size n == 2^k-1 for some k>=0.

fn main() {}

}