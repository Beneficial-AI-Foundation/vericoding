// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn power(base: int, exp: int) -> int
    decreases exp
{
    if exp <= 0 { 1 }
    else { base * power(base, exp - 1) }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): [no changes] */
proof fn lemma_lcm_is_smallest(n: int, p: int, found_val: int, i: int)
    requires
        n > 0,
        p > 0,
        i > 0,
        found_val == i * p,
        found_val % n == 0,
        forall|j: int| 1 <= j < i ==> (j * p) % n != 0,
    ensures
        forall|m: int| (m > 0 && m % n == 0 && m % p == 0) ==> found_val <= m,
{
    assert forall|m: int| m > 0 && m % n == 0 && m % p == 0 implies found_val <= m by {
        vstd::arithmetic::div_mod::lemma_mod_is_zero(m, p);
        let k = m / p;
        assert(m == p * k);

        assert(k > 0) by {
            if k <= 0 {
                vstd::arithmetic::mul::lemma_mul_is_nonpositive(p, k);
                assert(m <= 0);
                assert(false);
            }
        };

        assert((p * k) % n == 0);
        assert(k >= i) by {
            if k < i {
                assert(k >= 1);
                assert((k * p) % n != 0);
                assert(false);
            }
        };

        vstd::arithmetic::mul::lemma_mul_is_monotonic(i, k, p);
        assert(i * p <= k * p);
        assert(found_val <= m);
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, k: i8) -> (result: i8)
    requires 
        n > 0 && k >= 0,
    ensures 
        result > 0,
        (result as int) % (n as int) == 0,
        (result as int) % power(10, k as int) == 0,
        forall|m: int| #[trigger] (m % (n as int)) == 0 && #[trigger] (m % power(10, k as int)) == 0 && m > 0 ==> (result as int) <= m,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): [fix syntax error: `ghost let` -> `let ghost`] */
{
    let n_i64 = n as i64;

    let ghost n_int = n as int;
    let ghost k_int = k as int;
    let ghost p10k_int = power(10, k_int);

    let mut p10k: i64 = 1;
    let mut j: i8 = 0;
    while j < k
        invariant
            p10k == power(10, j as int),
            p10k > 0,
            j <= k,
    {
        p10k = p10k * 10;
        j = j + 1;
    }

    let mut i: i64 = 1;
    loop
        invariant
            n > 0,
            k >= 0,
            n_i64 == n_int,
            p10k == p10k_int,
            p10k > 0,
            i > 0,
            i <= n_i64,
            forall|j_int: int| 1 <= j_int < i as int ==> (j_int * p10k_int) % n_int != 0,
        decreases n_i64 - i,
    {
        let candidate = i * p10k;
        if candidate % n_i64 == 0 {
            proof {
                let found_val_int = candidate as int;
                let i_int = i as int;
                
                assert(found_val_int == i_int * p10k_int) by {
                    assert(i * p10k == (i as int) * (p10k as int));
                }

                lemma_lcm_is_smallest(n_int, p10k_int, found_val_int, i_int);
            }
            return candidate as i8;
        }
        i = i + 1;
    }
}
// </vc-code>


}

fn main() {}