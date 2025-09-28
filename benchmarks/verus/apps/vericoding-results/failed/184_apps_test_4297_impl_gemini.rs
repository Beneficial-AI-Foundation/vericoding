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
/* helper modified by LLM (iteration 4): [fixed library paths and simplified proof logic] */
proof fn lemma_sol_is_n_if_even(n: int)
    requires
        n >= 1,
        n % 2 == 0,
    ensures
        n % 2 == 0 && n % n == 0,
        is_smallest(n, n),
{
    assert(n % n == 0) by(nonlinear_arith) requires n != 0;
    assert forall|k: int| 1 <= k < n implies !((k % 2 == 0) && (k % n == 0)) by {
        if 1 <= k < n && k % 2 == 0 && k % n == 0 {
            vstd::arithmetic::div_mod::lemma_mod_p_when_less(k, n);
            assert(k % n == k);
            assert(k == 0);
            assert(false);
        }
    };
}

/* helper modified by LLM (iteration 4): [fixed library paths and simplified proof logic] */
proof fn lemma_sol_is_2n_if_odd(n: int)
    requires
        n >= 1,
        n % 2 != 0,
    ensures
        (2 * n) % 2 == 0 && (2 * n) % n == 0,
        is_smallest(2 * n, n),
{
    let result = 2 * n;
    assert(result % 2 == 0) by(nonlinear_arith);
    assert(result % n == 0) by(nonlinear_arith) requires n != 0;

    assert forall|k: int| 1 <= k < result implies !((k % 2 == 0) && (k % n == 0)) by {
        if 1 <= k < result && k % 2 == 0 && k % n == 0 {
            vstd::math::lemma_gcd_of_odd_and_2(n);
            vstd::math::lemma_gcd_is_symmetric(n, 2);
            vstd::math::lemma_multiple_of_coprime(k, 2, n);
            assert(k % (2 * n) == 0);
            assert(k % result == 0);

            assert(result > 0) by(nonlinear_arith) requires n >= 1;
            vstd::arithmetic::div_mod::lemma_mod_p_when_less(k, result);
            assert(k % result == k);
            assert(k == 0);
            assert(false);
        }
    };
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
/* code modified by LLM (iteration 4): [fixed spec/exec type errors] */
{
    let ghost n_int = n as int;
    if n % 2 == 0 {
        lemma_sol_is_n_if_even(n_int);
        n
    } else {
        lemma_sol_is_2n_if_odd(n_int);
        n * 2
    }
}
// </vc-code>


}

fn main() {}