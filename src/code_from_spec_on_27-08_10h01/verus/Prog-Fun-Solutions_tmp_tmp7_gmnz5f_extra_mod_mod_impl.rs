use vstd::prelude::*;

verus! {

spec fn f(n: nat) -> nat
    decreases n
{
    if n == 0 { 1 }
    else if n % 2 == 0 { 1 + 2 * f(n / 2) }
    else { 2 * f(n / 2) }
}

// <vc-helpers>
proof fn f_decreases_lemma(n: nat)
    requires n > 0
    ensures n / 2 < n
{
    assert(n >= 1);
    assert(n / 2 < n) by(nonlinear_arith);
}

proof fn f_bounds_lemma(n: nat)
    ensures f(n) >= 1
    decreases n
{
    if n == 0 {
        assert(f(n) == 1);
    } else if n % 2 == 0 {
        f_bounds_lemma(n / 2);
        assert(f(n) == 1 + 2 * f(n / 2));
        assert(f(n / 2) >= 1);
        assert(f(n) >= 1 + 2 * 1 == 3);
    } else {
        f_bounds_lemma(n / 2);
        assert(f(n) == 2 * f(n / 2));
        assert(f(n / 2) >= 1);
        assert(f(n) >= 2 * 1 == 2);
    }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn mod_fn(n: u64) -> (a: u64)
    requires n >= 0,
    ensures a as nat == f(n as nat),
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    if n == 0 {
        1
    } else if n % 2 == 0 {
        let half_result = mod_fn(n / 2);
        proof {
            f_bounds_lemma(n as nat / 2);
        }
        1 + 2 * half_result
    } else {
        let half_result = mod_fn(n / 2);
        proof {
            f_bounds_lemma(n as nat / 2);
        }
        2 * half_result
    }
}
// </vc-code>

fn main() {}

}