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
proof fn is_2_pow_div_2_lemma(n: int)
    requires n > 1, is_2_pow(n)
    ensures is_2_pow(n / 2)
{
    // The property follows from the recursive definition
}

proof fn is_2_pow_half_lemma(n: int)
    requires n > 0, is_2_pow(n + 1)
    ensures n > 0 ==> is_2_pow((n + 1) / 2)
{
    if n > 0 {
        assert(n + 1 > 1);
        assert(is_2_pow(n + 1));
        is_2_pow_div_2_lemma(n + 1);
        assert(is_2_pow((n + 1) / 2));
    }
}

proof fn binary_search_bounds_lemma(left: usize, right: usize, i: usize, n: usize)
    requires i <= left < right <= i + n
    ensures left + (right - left) / 2 < right
{
}

proof fn power_of_two_split_lemma(size: int)
    requires size > 0, is_2_pow(size)
    ensures size > 1 ==> is_2_pow((size + 1) / 2)
{
    if size > 1 {
        assert(size % 2 == 0);
        assert(size / 2 >= 1);
        assert(is_2_pow(size / 2));
        assert((size + 1) / 2 == size / 2);
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
    let mut left = i;
    let mut right = i + n;
    
    while left < right
        invariant
            i <= left <= right <= i + n,
            forall|r: int| i <= r < left && 0 <= r < a.len() ==> a@[r] < x,
            forall|r: int| right <= r < (i + n) && 0 <= r < a.len() ==> a@[r] >= x,
            is_2_pow((right - left + 1) as int),
        decreases right - left
    {
        let mid = left + (right - left) / 2;
        
        assert(left <= mid < right);
        assert(mid < right);
        assert(right <= i + n);
        assert(i + n <= a.len());
        assert(mid < a.len());
        
        if a[mid] < x {
            let old_size = (right - left + 1) as int;
            left = mid + 1;
            
            proof {
                assert(is_2_pow(old_size));
                assert(old_size > 0);
                power_of_two_split_lemma(old_size);
                if old_size > 1 {
                    assert(is_2_pow((old_size + 1) / 2));
                    assert((right - left + 1) as int == (old_size + 1) / 2);
                }
            }
        } else {
            let old_size = (right - left + 1) as int;
            right = mid;
            
            proof {
                assert(is_2_pow(old_size));
                assert(old_size > 0);
                power_of_two_split_lemma(old_size);
                if old_size > 1 {
                    assert(is_2_pow((old_size + 1) / 2));
                    assert((right - left + 1) as int == (old_size + 1) / 2);
                }
            }
        }
    }
    
    left
}
// </vc-code>

// This method is a binary search that only works for array
// segments of size n == 2^k-1 for some k>=0.

fn main() {}

}