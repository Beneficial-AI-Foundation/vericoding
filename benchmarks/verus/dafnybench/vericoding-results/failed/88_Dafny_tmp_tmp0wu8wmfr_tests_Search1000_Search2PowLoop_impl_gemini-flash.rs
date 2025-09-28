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
spec fn power2(n: nat) -> nat
    decreases n
{
    if n == 0 {
        1
    } else {
        2 * power2(n - 1)
    }
}

proof fn lemma_is_2_pow_nat(n: nat)
    requires is_2_pow(n as int)
    ensures exists k: nat . n == power2(k)
{
    if n == 1 {
        assert(n == power2(0));
    } else {
        assert(n > 0);
        assert(n % 2 == 0);
        lemma_is_2_pow_nat((n / 2) as nat);
        assert(exists k_prime: nat . (n / 2) as nat == power2(k_prime));
        let k_prime = ((n / 2) as nat).choose(|k_prime: nat| (n / 2) as nat == power2(k_prime));
        assert(n == 2 * (n / 2) as nat);
        assert(n == 2 * power2(k_prime));
        assert(n == power2(k_prime + 1));
        assert(exists k: nat . n == power2(k));
    }
}

proof fn lemma_power2_pos(k: nat)
    ensures power2(k) > 0
{
    if k == 0 {
        assert(power2(0) == 1);
    } else {
        lemma_power2_pos(k - 1);
        assert(power2(k) == 2 * power2(k - 1));
        assert(power2(k - 1) > 0);
        assert(power2(k) > 0);
    }
}

proof fn lemma_power2_monotonic(k: nat)
    ensures power2(k+1) > power2(k)
{
    lemma_power2_pos(k);
    assert(power2(k+1) == 2 * power2(k));
    assert(2 * power2(k) > power2(k));
}

proof fn lemma_power2_div2(k: nat)
    requires k > 0
    ensures power2(k) / 2 == power2(k-1)
{
    assert(power2(k) == 2 * power2(k-1));
    assert(power2(k) / 2 == power2(k-1));
}

proof fn lemma_is_2_pow_is_power2(n_val: int) 
    requires n_val > 0, is_2_pow(n_val)
    ensures exists k: nat . n_val == power2(k)
{
    lemma_is_2_pow_nat(n_val as nat);
}

proof fn lemma_is_2_pow_implies_odd(n_val: int) 
    requires n_val > 0, is_2_pow(n_val)
    ensures (n_val - 1) % 2 == 0
{
    if n_val == 1 {
        assert((n_val - 1) % 2 == 0);
    } else {
        assert(is_2_pow(n_val / 2));
        assert(n_val % 2 == 0);
        lemma_is_2_pow_implies_odd(n_val / 2);
        assert(((n_val / 2) - 1) % 2 == 0);
        assert(n_val / 2 - 1 == 2 * (((n_val / 2) - 1) / 2));
        assert(n_val - 2 == 4 * (((n_val / 2) - 1) / 2));
        assert(n_val - 1 == 4 * (((n_val / 2) - 1) / 2) + 1);
        assert((n_val - 1) / 2 == 2 * (((n_val / 2) - 1) / 2) + (1 / 2)); // This implies n_val-1 is not always int.
        assert(n_val % 2 == 0); // n_val is even
        assert((n_val - 1) % 2 == 1); // n_val - 1 is odd
    }
}

proof fn lemma_is_2_pow_minus_1_char(n: nat)
    requires is_2_pow((n + 1) as int)
    ensures (n % 2 == 1) || (n == 0)
{
    if n == 0 {
        // (0+1) as int = 1, is_2_pow(1) is true. 0 % 2 == 0.
    } else {
        // if n > 0, then n+1 > 1.
        // since is_2_pow(n+1) and n+1 > 1, n+1 must be even.
        // therefore n must be odd.
        assert((n + 1) % 2 == 0);
        assert(n % 2 == 1);
    }
}

proof fn lemma_is_2_pow_div_2_char(n: nat)
    requires (n > 0) && (is_2_pow((n + 1) as int))
    ensures is_2_pow(((n - 1) / 2 + 1) as int)
{
    lemma_is_2_pow_minus_1_char(n); // To prove n is odd if n > 0
    if n > 0 {
        assert(n % 2 == 1); // n is odd
        let m = (n + 1) as int; // m is even
        assert(is_2_pow(m));
        assert(m % 2 == 0);
        assert(is_2_pow(m / 2)); // (n+1) / 2
        assert((n - 1) / 2 + 1 == (n + 1) / 2);
        assert(is_2_pow(((n + 1) / 2) as int));
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
    let mut lo: usize = i;
    let mut hi: usize = i + n;

    proof {
        lemma_is_2_pow_is_power2((n + 1) as int);
    }

    while lo < hi
        invariant
            i <= lo <= hi <= i + n,
            // The segment [lo, hi) where the element could be
            // It means that for 'r' in [i, lo), a[r] < x
            // And for 'r' in [hi, i+n), a[r] >= x
            forall|r: int| (i <= r < lo && 0 <= r < a.len()) ==> a@[r] < x,
            forall|r: int| (hi <= r < (i + n) && 0 <= r < a.len()) ==> a@[r] >= x,
            is_2_pow(((hi - lo) + 1) as int), // The size of the search space (hi-lo) + 1 must always be a power of 2
    {
        proof {
            if hi - lo > 0 {
                lemma_is_2_pow_minus_1_char((hi - lo) as nat);
            }
        }
        let mid: usize = lo + ((hi - lo + 1) / 2) - 1;

        if a@[mid] < x {
            lo = mid + 1;
            proof {
                assert(mid + 1 <= hi); // This is needed to prove lo <= hi for the next iteration
                assert((hi - (mid + 1) + 1) as int == (hi - mid) as int);

                let diff = hi - lo + 1;
                let new_diff = hi - (mid + 1) + 1;

                assert(mid == lo + (diff / 2) - 1);
                assert(mid + 1 == lo + (diff / 2));

                assert(new_diff == hi - (lo + (diff / 2)) + 1);
                assert(new_diff == (hi - lo + 1) - (diff / 2));
                assert(new_diff == diff - diff / 2);

                if (hi - lo) as nat > 0 {
                    lemma_is_2_pow_minus_1_char((hi - lo) as nat);
                    assert((hi - lo) % 2 == 1); // hi-lo is odd
                } else {
                    assert((hi - lo) == 0); // hi-lo is zero, ((hi-lo)+1) is 1. new_diff will be 0.
                }

                if (hi-lo) % 2 == 1 { // diff is even
                    assert(diff / 2 == (diff - 1) / 2 + 1);
                    assert(diff - diff / 2 == diff - ((diff-1)/2 + 1));
                    assert(diff - ((diff-1)/2 + 1) == diff - (diff-1)/2 - 1);
                    assert(diff - (diff-1)/2 - 1 == (2*diff - diff + 1)/2 - 1);
                    assert((diff+1)/2 - 1 == (diff-1)/2);
                    assert(new_diff == (diff+1)/2);
                    lemma_is_2_pow_div_2_char((hi - lo) as nat);
                    assert(is_2_pow(((hi - lo + 1) / 2) as int));
                } else { // diff is odd, so hi-lo is even (only if hi-lo=0)
                    assert( (hi-lo) == 0 ); // diff is 1
                    assert( (hi-lo+1) == 1 );
                    assert( diff / 2 == 0);
                    assert( new_diff == 1 - 0);
                    assert( new_diff == 1);
                    assert( is_2_pow(1));
                }

            }
        } else {
            hi = mid;
            proof {
                assert(lo <= mid); // This is needed to prove lo <= hi for the next iteration
                let diff = hi - lo + 1;
                assert((mid - lo + 1) as int == (diff / 2) as int);
                if (hi-lo) % 2 == 1 { // diff is even
                    lemma_is_2_pow_div_2_char((hi - lo) as nat);
                    assert(is_2_pow(((hi - lo + 1) / 2) as int));
                } else { // diff is odd
                    assert( (hi-lo) == 0 );
                    assert( (hi-lo+1) == 1 );
                    assert( (mid - lo + 1) == 1);
                    assert( is_2_pow(1));
                }
            }
        }
    }
    lo
}
// </vc-code>

// This method is a binary search that only works for array
// segments of size n == 2^k-1 for some k>=0.

fn main() {}

}