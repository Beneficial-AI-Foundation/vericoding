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
proof fn is_2_pow_div2(t: int)
    requires
        t > 1,
        is_2_pow(t),
    ensures
        is_2_pow(t / 2),
    ensures
        t % 2 == 0
{
    // By definition of is_2_pow for t > 1 we have t % 2 == 0 && is_2_pow(t/2)
    assert(t % 2 == 0);
    assert(is_2_pow(t / 2));
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
        i
    } else {
        let m: usize = n / 2;
        let mid: usize = i + m;

        proof {
            let ni: int = n as int;
            let mi: int = m as int;

            // n != 0 because we are in the else branch
            assert(ni > 0);
            assert(mi == ni / 2);
            // For ni > 0, ni/2 < ni, so m < n
            assert(mi < ni);
            assert(m < n);

            // Bound on the whole segment from the precondition
            assert(i + n <= a.len());
            // mid = i + m and m < n implies mid < i + n, so mid < a.len()
            assert(mid < a.len());
        }

        if a[mid] < x {
            proof {
                let ni: int = n as int;
                let mi: int = m as int;
                let t: int = (n + 1) as int;

                assert(ni > 0);
                assert(t == ni + 1);
                assert(t > 1);
                is_2_pow_div2(t);
                assert(t % 2 == 0);
                assert(is_2_pow(t / 2));

                assert(ni == 2*(ni / 2) + (ni % 2));
                assert(mi == ni / 2);
                assert(ni == 2*mi + (ni % 2));
                assert((ni + 1) % 2 == 0);
                assert(ni % 2 == 1);
                assert(ni == 2*mi + 1);
                assert(n == 2*m + 1);
                assert(i + n == (mid + 1) + m);

                assert(t / 2 == (m + 1) as int);
                assert(is_2_pow((m + 1) as int));

                // Ensure recursive preconditions for the right half
                assert((mid + 1) + m <= a.len());
                assert(m < n);

                assert(forall|p: int, q: int|
                    0 <= p < q && (mid + 1) as int <= p && q < ((mid + 1) + m) as int ==>
                        a[p] <= a[q]);
            }
            let k = search_2_pow_recursive(a, mid + 1, m, x);
            k
        } else {
            proof {
                let ni: int = n as int;
                let mi: int = m as int;
                let t: int = (n + 1) as int;

                assert(ni > 0);
                assert(t == ni + 1);
                assert(t > 1);
                is_2_pow_div2(t);
                assert(t % 2 == 0);
                assert(is_2_pow(t / 2));

                assert(ni == 2*(ni / 2) + (ni % 2));
                assert(mi == ni / 2);
                assert(ni == 2*mi + (ni % 2));
                assert((ni + 1) % 2 == 0);
                assert(ni % 2 == 1);
                assert(ni == 2*mi + 1);
                assert(n == 2*m + 1);
                assert(i + n == i + 2*m + 1);
                assert(i + n == i + m + m + 1);

                assert(t / 2 == (m + 1) as int);
                assert(is_2_pow((m + 1) as int));

                // Ensure recursive preconditions for the left half
                assert(i + m <= a.len());
                assert(m < n);

                assert(forall|p: int, q: int|
                    0 <= p < q && i as int <= p && q < (i + m) as int ==>
                        a[p] <= a[q]);
            }
            let k = search_2_pow_recursive(a, i, m, x);
            k
        }
    }
}
// </vc-code>

fn main() {}

}