// <vc-preamble>
use vstd::prelude::*;

verus! {

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
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed incorrect paths to arithmetic lemmas */
proof fn lemma_is_2_pow_half(n: int)
    requires
        n > 0,
        is_2_pow(n + 1),
    ensures
        is_2_pow(n / 2 + 1),
{
    // Since n > 0, n + 1 > 1. Unfolding is_2_pow reveals (n+1)%2==0 and is_2_pow((n+1)/2).
    assert(is_2_pow((n + 1) / 2));

    // To satisfy the ensures clause, we prove that (n+1)/2 == n/2 + 1.
    assert((n + 1) / 2 == n / 2 + 1) by {
        // From (n+1)%2 == 0, it follows that n is odd, so n%2 == 1.
        assert(n % 2 == 1) by {};

        // By Euclidean division, n = 2 * (n/2) + n%2.
        vstd::arithmetic::lemmas::lemma_div_mod(n, 2);
        assert(n == 2 * (n/2) + 1);

        // So, n+1 = 2*(n/2) + 2 = 2*(n/2 + 1).
        assert(n + 1 == 2 * (n/2 + 1));
        
        // The lemma div_of_mul shows that (2*x)/2 == x.
        vstd::arithmetic::mul::lemma_div_of_mul(n/2 + 1, 2);
        assert((2 * (n/2 + 1)) / 2 == n/2 + 1);
    };

    assert(is_2_pow(n / 2 + 1));
}
// </vc-helpers>

// <vc-spec>
fn search_2_pow_recursive(a: &[i32], i: usize, n: usize, x: i32) -> (k: usize)
    requires
        i + n <= a.len(),
        ({(forall|p: int, q: int|
            0 <= p < q && i as int <= p && q < (i + n) as int ==> 
            a[p] <= a[q])}),
        is_2_pow((n + 1) as int),
    ensures
        i <= k <= i + n,
        ({(forall|r: int|
            0 <= r && i as int <= r < k as int ==> 
            a[r] < x)}),
        ({(forall|r: int|
            0 <= r && k as int <= r < (i + n) as int ==> 
            a[r] >= x)}),
    decreases n
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): no changes to logic, helper compilation fix is primary */
{
    if n == 0 {
        return i;
    }

    let m = n / 2;
    let mid = i + m;

    proof {
        lemma_is_2_pow_half(n as int);
    }

    if a[mid] < x {
        assert forall|r: int| (i as int) <= r && r <= (mid as int) implies a@[r] <= a@[mid as int] by {};
        search_2_pow_recursive(a, mid + 1, m, x)
    } else {
        assert forall|r: int| (mid as int) <= r && r < ((i + n) as int) implies a@[mid as int] <= a@[r] by {};
        search_2_pow_recursive(a, i, m, x)
    }
}
// </vc-code>

}
fn main() {}