// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(n: int) -> bool {
    n >= 1
}

spec fn divisible_by_both(result: int, n: int) -> bool
    recommends n >= 1
{
    result % 2 == 0 && result % n == 0
}

spec fn is_smallest(result: int, n: int) -> bool
    recommends n >= 1
{
    forall|k: int| 1 <= k < result ==> !(#[trigger] (k % 2) == 0 && #[trigger] (k % n) == 0)
}

spec fn lcm(a: int, b: int) -> int
    recommends a >= 1 && b >= 1
{
    if a % b == 0 {
        a
    } else if b % a == 0 {
        b
    } else {
        a * b
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): lemma that if 0 <= k < n and k % n == 0 then k == 0 */
proof fn zero_mod_smaller(k: int, n: int)
    requires
        n >= 1,
        0 <= k < n,
        k % n == 0,
    ensures
        k == 0,
{
    // For 0 <= k < n, k % n == k, so k == 0
    assert(k % n == k);
    assert(k == 0);
}

/* helper modified by LLM (iteration 5): proves that the least positive even multiple of n is n if n is even, otherwise 2*n */
proof fn smallest_even_multiple(n: int)
    requires
        n >= 1,
    ensures
        (if n % 2 == 0 { n } else { 2 * n }) >= 1,
        (if n % 2 == 0 { n } else { 2 * n }) % 2 == 0 && (if n % 2 == 0 { n } else { 2 * n }) % n == 0,
        is_smallest((if n % 2 == 0 { n } else { 2 * n }), n),
        (n % 2 == 0 ==> (if n % 2 == 0 { n } else { 2 * n }) == n),
        (n % 2 != 0 ==> (if n % 2 == 0 { n } else { 2 * n }) == n * 2),
{
    let r = if n % 2 == 0 { n } else { 2 * n };
    assert(r >= 1);
    if n % 2 == 0 {
        assert(r == n);
        assert(r % 2 == 0);
        assert(r % n == 0);
        proof {
            forall|k: int| {
                if 1 <= k && k < r {
                    assert(0 <= k && k < n);
                    assert(k % n == k);
                    if k % n == 0 {
                        zero_mod_smaller(k, n);
                        assert(k == 0);
                        // contradicts 1 <= k
                        assert(1 <= k);
                        assert(false);
                    } else {
                        assert(!(k % n == 0 && k % 2 == 0));
                    }
                } else {
                    assert(true);
                }
            };
        }
    } else {
        assert(r == 2 * n);
        assert(r % 2 == 0);
        assert(r % n == 0);
        proof {
            forall|k: int| {
                if 1 <= k && k < r {
                    if k < n {
                        assert(0 <= k && k < n);
                        assert(k % n == k);
                        if k % n == 0 {
                            zero_mod_smaller(k, n);
                            assert(k == 0);
                            assert(false);
                        } else {
                            assert(!(k % n == 0 && k % 2 == 0));
                        }
                    } else {
                        assert(n <= k && k < 2 * n);
                        assert(0 <= k - n && k - n < n);
                        assert(k % n == k - n);
                        if k % n == 0 {
                            assert(k - n == 0);
                            assert(k == n);
                            assert(n % 2 != 0);
                            assert(k % 2 == n % 2);
                            assert(false);
                        } else {
                            assert(!(k % n == 0 && k % 2 == 0));
                        }
                    }
                } else {
                    assert(true);
                }
            };
        }
    }
    assert(n % 2 == 0 ==> r == n);
    assert(n % 2 != 0 ==> r == 2 * n);
}

// </vc-helpers>

// <vc-spec>
fn solve(n: i8) -> (result: i8)
    requires 
        n >= 1,
    ensures 
        result >= 1,
        result as int % 2 == 0 && result as int % n as int == 0,
        forall|k: int| 1 <= k < result as int ==> !(#[trigger] (k % 2) == 0 && #[trigger] (k % n as int) == 0),
        (n as int % 2 == 0 ==> result as int == n as int) && (n as int % 2 != 0 ==> result as int == n as int * 2),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): compute smallest even multiple using i8 arithmetic and invoke ghost lemma in proof */
    let result: i8 = if n % 2 == 0 { n } else { n * 2 };
    proof {
        let ni: int = n as int;
        smallest_even_multiple(ni);
        let rint: int = if ni % 2 == 0 { ni } else { 2 * ni };
        assert(result as int == rint);
    }
    result
}
// </vc-code>


}

fn main() {}