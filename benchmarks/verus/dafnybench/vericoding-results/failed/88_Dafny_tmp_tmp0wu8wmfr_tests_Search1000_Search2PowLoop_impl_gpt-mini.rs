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
proof fn pow2_even_div(n: int)
    requires is_2_pow(n) && n > 1
    ensures n % 2 == 0
{
    // By the definition of is_2_pow, when n > 1 it must be n % 2 == 0 && is_2_pow(n/2)
    assert(n % 2 == 0);
}

proof fn pow2_half(n: int)
    requires is_2_pow(n) && n > 1
    ensures is_2_pow(n / 2)
{
    // By unfolding the definition of is_2_pow for n > 1
    assert(is_2_pow(n / 2));
}

proof fn pow2_div_relation(n: int)
    requires is_2_pow(n + 1) && n >= 1
    ensures (n / 2) + 1 == ((n + 1) / 2)
{
    // From is_2_pow(n+1) and n+1 > 1 we know n+1 is even.
    pow2_even_div(n + 1);
    assert((n + 1) % 2 == 0);
    // Hence n is odd.
    assert(n % 2 == 1);
    // Let m = (n+1)/2. Then 2*m == n+1.
    let m = (n + 1) / 2;
    assert(m * 2 == n + 1);
    // From 2*m == n+1 we get n = 2*m - 1, so n/2 == m - 1 (integer division).
    assert(n / 2 == m - 1);
    // Therefore (n/2) + 1 == m == (n+1)/2.
    assert((n / 2) + 1 == m);
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
    let mut low: usize = i;
    let mut len: usize = n;
    while len != 0
        invariant
            i <= low && low <= i + n,
            low + len <= i + n,
            i + n <= a.len(),
            forall|r: int| i as int <= r && r < low as int && 0 <= r && r < a.len() as int ==> a@[r] < x,
            forall|r: int| (low + len) as int <= r && r < (i + n) as int && 0 <= r && r < a.len() as int ==> a@[r] >= x,
            is_2_pow((len + 1) as int),
        decreases len
    {
        // len != 0 ensures len >= 1
        assert(len >= 1);

        let old_low = low;
        let old_len = len;

        // compute mid and prove it's in bounds for indexing
        let mid = low + len / 2;

        // len/2 < len for len >= 1
        assert(len / 2 < len);
        // so mid < low + len
        assert(mid < low + len);
        // low + len <= i + n by invariant, and i + n <= a.len() by invariant
        assert(low + len <= i + n);
        assert(i + n <= a.len());
        // combine to get mid < a.len()
        assert(mid < a.len());

        if a[mid] < x {
            // ensure arithmetic won't underflow when computing new len
            assert(old_len >= (old_len / 2) + 1);
            // mid + 1 <= old_low + old_len ensures mid+1 is within array bounds
            assert(mid + 1 <= old_low + old_len);

            let new_len = old_len - (old_len / 2) - 1;

            // Prove the new is_2_pow((new_len+1) as int) fact using helper lemmas
            proof {
                // relate old_len and current len to use the loop invariant
                assert(old_len == len);
                // old_len >= 1 (since len >= 1)
                assert(old_len >= 1);
                // Use lemmas about powers of two
                assert(is_2_pow((old_len + 1) as int));
                pow2_div_relation(old_len as int);
                pow2_even_div((old_len + 1) as int);
                pow2_half((old_len + 1) as int);
                // Show arithmetic relation: (new_len + 1) == ((old_len + 1) / 2)
                assert((new_len + 1) as int == ((old_len as int + 1) / 2));
                assert(is_2_pow((new_len + 1) as int));
            }

            low = mid + 1;
            len = new_len;

            // low + len equals the old upper bound
            assert((low + len) == (old_low + old_len));
        } else {
            // shrink to left half
            let new_len = old_len / 2;

            // Prove the new is_2_pow((new_len+1) as int)
            proof {
                assert(old_len == len);
                assert(old_len >= 1);
                assert(is_2_pow((old_len + 1) as int));
                pow2_div_relation(old_len as int);
                pow2_even_div((old_len + 1) as int);
                pow2_half((old_len + 1) as int);
                assert((new_len + 1) as int == ((old_len as int + 1) / 2));
                assert(is_2_pow((new_len + 1) as int));
            }

            // low unchanged so low + len <= old_low + old_len
            len = new_len;
            assert(low + len <= old_low + old_len);
        }
    }
    low
}
// </vc-code>

// This method is a binary search that only works for array
// segments of size n == 2^k-1 for some k>=0.

fn main() {}

}