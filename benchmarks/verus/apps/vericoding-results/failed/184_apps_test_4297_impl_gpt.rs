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
/* helper modified by LLM (iteration 5): basic modulo lemmas and LCM(2,n) properties */
proof fn lemma_mod_self_zero(n: int)
    requires
        n >= 1,
    ensures
        n % n == 0,
{
    assert(n % n == 0);
}

/* helper modified by LLM (iteration 5): (k*n) % n == 0 for n>=1 */
proof fn lemma_mod_mul_zero(k: int, n: int)
    requires
        n >= 1,
    ensures
        (k * n) % n == 0,
{
    assert((k * n) % n == 0);
}

/* helper modified by LLM (iteration 5): if 0 <= a < n and n>=1 then a % n == a */
proof fn lemma_mod_in_range_identity(a: int, n: int)
    requires
        n >= 1,
        0 <= a,
        a < n,
    ensures
        a % n == a,
{
    assert(a % n == a);
}

/* helper modified by LLM (iteration 5): (a + n) % n == a % n for n>=1 */
proof fn lemma_mod_add_n(a: int, n: int)
    requires
        n >= 1,
    ensures
        (a + n) % n == a % n,
{
    assert((a + n) % n == a % n);
}

/* helper modified by LLM (iteration 5): prove divisibility of the computed LCM(2, n) */
proof fn lemma_lcm2_divisible(n: int)
    requires
        n >= 1,
    ensures
        divisible_by_both(if n % 2 == 0 { n } else { n * 2 }, n),
{
    if n % 2 == 0 {
        let r = n;
        assert(r % 2 == 0);
        lemma_mod_self_zero(n);
        assert(r % n == 0);
    } else {
        let r = 2 * n;
        assert(r == n * 2);
        lemma_mod_mul_zero(n, 2);
        assert((n * 2) % 2 == 0);
        assert(r % 2 == 0);
        lemma_mod_mul_zero(2, n);
        assert(r % n == 0);
    }
}

/* helper modified by LLM (iteration 5): prove minimality (no smaller common multiple) */
proof fn lemma_lcm2_smallest(n: int)
    requires
        n >= 1,
    ensures
        is_smallest(if n % 2 == 0 { n } else { n * 2 }, n),
{
    let r = if n % 2 == 0 { n } else { 2 * n };
    assert forall|k: int| 1 <= k && k < r implies !(#[trigger] (k % 2) == 0 && #[trigger] (k % n) == 0) by {
        if 1 <= k && k < r {
            if n % 2 == 0 {
                if (k % 2 == 0) && (k % n == 0) {
                    assert(0 <= k);
                    lemma_mod_in_range_identity(k, n);
                    assert(k % n == k);
                    assert(k != 0);
                    assert(!(k % n == 0));
                }
            } else {
                if (k % 2 == 0) && (k % n == 0) {
                    if k < n {
                        assert(0 <= k);
                        lemma_mod_in_range_identity(k, n);
                        assert(k % n == k);
                        assert(k != 0);
                        assert(!(k % n == 0));
                    } else {
                        let m = k - n;
                        assert(0 <= m);
                        assert(m < n);
                        lemma_mod_add_n(m, n);
                        assert(k % n == m % n);
                        assert(m % n == 0);
                        lemma_mod_in_range_identity(m, n);
                        assert(m == 0);
                        assert(k == n);
                        assert(n % 2 != 0);
                        assert(k % 2 == n % 2);
                        assert(k % 2 != 0);
                    }
                }
            }
        }
    }
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
    /* code modified by LLM (iteration 5): avoid non-ghost use of 'int'; keep arithmetic in exec i8, proofs in ghost */
    let result: i8 = if n % 2 == 0 { n } else { n * 2 };

    proof {
        let ni: int = n as int;
        let ri: int = if ni % 2 == 0 { ni } else { 2 * ni };

        // Prove divisibility and minimality for the mathematical result
        lemma_lcm2_divisible(ni);
        lemma_lcm2_smallest(ni);

        // Connect the executable result with the mathematical value
        if ni % 2 == 0 {
            assert(result as int == ni);
        } else {
            assert(result as int == 2 * ni);
        }

        assert(divisible_by_both(result as int, ni));
        assert(is_smallest(result as int, ni));
        assert(ri >= 1);
        assert(result as int >= 1);
    }

    result
}
// </vc-code>


}

fn main() {}