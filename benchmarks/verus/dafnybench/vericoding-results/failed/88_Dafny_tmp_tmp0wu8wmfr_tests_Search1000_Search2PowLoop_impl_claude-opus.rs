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
// Helper lemma to prove that if n+1 is a power of 2 and n >= 1, then (n-1)/2 + 1 is also a power of 2
proof fn power_of_2_div_property(n: nat)
    requires
        n >= 1,
        is_2_pow((n + 1) as int),
    ensures
        is_2_pow((((n - 1) / 2) + 1) as int),
    decreases n
{
    // Since n+1 is a power of 2 and n >= 1, we have n+1 >= 2
    // So n+1 = 2^k for some k >= 1
    // This means n = 2^k - 1
    // Therefore (n-1)/2 = (2^k - 2)/2 = 2^(k-1) - 1
    // So ((n-1)/2) + 1 = 2^(k-1), which is a power of 2
    if n == 1 {
        assert(((n - 1) / 2) + 1 == 1);
        assert(is_2_pow(1));
    } else {
        assert(n > 1);
        let n_plus_1 = (n + 1) as int;
        assert(n_plus_1 % 2 == 0);
        assert(is_2_pow(n_plus_1 / 2));
        assert((n - 1) / 2 == (n_plus_1 / 2 - 1));
        assert(((n - 1) / 2) + 1 == n_plus_1 / 2);
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
    if n == 0 {
        return i;
    }
    
    let mut k: usize = i;
    let mut m: usize = n;
    
    while m > 0
        invariant
            i <= k <= i + n,
            0 <= m <= n,
            k + m == i + n,
            is_2_pow((m + 1) as int),
            forall|r: int| i <= r < k && 0 <= r < a.len() ==> a@[r] < x,
            forall|r: int| k + m <= r < i + n && 0 <= r < a.len() ==> a@[r] >= x,
        decreases m
    {
        let step: usize = (m - 1) / 2;
        
        assert(k + step < usize::MAX) by {
            assert(step <= m - 1);
            assert(k + m <= i + n);
            assert(i + n <= a.len());
            assert(a.len() <= usize::MAX);
        }
        
        let mid: usize = k + step;
        
        assert(mid < a.len()) by {
            assert(step == (m - 1) / 2);
            assert(step < m);
            assert(k + m <= i + n);
            assert(i + n <= a.len());
            assert(mid == k + step);
            assert(mid < k + m);
            assert(mid <= i + n - 1);
            assert(mid < a.len());
        }
        
        if a[mid] < x {
            proof {
                power_of_2_div_property(m as nat);
                assert(forall|r: int| k <= r <= mid && 0 <= r < a.len() ==> a@[r] < x) by {
                    assert forall|r: int| k <= r <= mid && 0 <= r < a.len() implies a@[r] < x by {
                        if r == mid as int {
                            assert(a@[r] == a@[mid as int]);
                        } else {
                            assert(k <= r < mid);
                            assert(a@[r] <= a@[mid as int]);
                        }
                    }
                }
                assert(mid + 1 + step == k + m) by {
                    assert(mid == k + step);
                    assert(step == (m - 1) / 2);
                    assert(m == 2 * step + 1);
                }
            }
            k = mid + 1;
            m = step;
        } else {
            proof {
                power_of_2_div_property(m as nat);
                assert(forall|r: int| mid <= r < k + m && 0 <= r < a.len() ==> a@[r] >= x) by {
                    assert forall|r: int| mid <= r < k + m && 0 <= r < a.len() implies a@[r] >= x by {
                        if r == mid as int {
                            assert(a@[r] == a@[mid as int]);
                        } else {
                            assert(mid < r < k + m);
                            assert(a@[mid as int] <= a@[r]);
                        }
                    }
                }
                assert(k + step == k + m) by {
                    assert(mid == k + step);
                    assert(step == (m - 1) / 2);
                    assert(m == 2 * step + 1);
                }
            }
            m = step;
        }
    }
    
    k
}
// </vc-code>

// This method is a binary search that only works for array
// segments of size n == 2^k-1 for some k>=0.

fn main() {}

}