// <vc-preamble>
use vstd::prelude::*;
use vstd::arithmetic::power::pow;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): power addition property */
fn pow_4_add(a: nat, b: nat)
    ensures
        pow(4, a + b) == pow(4, a) * pow(4, b),
{
    if b == (0: nat) {
        assert(a + (0: nat) == a);
        assert(pow(4, a + (0: nat)) == pow(4, a));
        assert(pow(4, (0: nat)) == 1);
        assert(pow(4, a) * pow(4, (0: nat)) == pow(4, a) * 1);
    } else {
        pow_4_add(a, b - (1: nat));
        assert(a + b == (a + (b - (1: nat))) + (1: nat));
        assert(pow(4, (a + (b - (1: nat))) + (1: nat)) == pow(4, a + (b - (1: nat))) * pow(4, (1: nat)));
        assert(pow(4, a + (b - (1: nat))) == pow(4, a) * pow(4, b - (1: nat)));
        assert(pow(4, a + b) == (pow(4, a) * pow(4, b - (1: nat))) * pow(4, (1: nat)));
        assert((pow(4, a) * pow(4, b - (1: nat))) * pow(4, (1: nat)) == pow(4, a) * (pow(4, b - (1: nat)) * pow(4, (1: nat))));
        assert(pow(4, b - (1: nat)) * pow(4, (1: nat)) == pow(4, (b - (1: nat)) + (1: nat)));
        assert(pow(4, (b - (1: nat)) + (1: nat)) == pow(4, b));
        assert(pow(4, a + b) == pow(4, a) * pow(4, b));
    }
}

/* helper modified by LLM (iteration 5): powers are at least 1 */
fn pow_ge1(s: nat)
    ensures
        pow(4, s) >= 1,
{
    if s == (0: nat) {
        assert(pow(4, (0: nat)) == 1);
    } else {
        pow_ge1(s - (1: nat));
        assert(pow(4, s) == pow(4, s - (1: nat)) * pow(4, (1: nat)));
        assert(pow(4, s - (1: nat)) >= 1);
        assert(pow(4, s) >= 1);
    }
}

/* helper modified by LLM (iteration 5): factorization lemma for powers of 4 */
fn pow4_divide_factor(m: nat, t: nat, x: nat)
    requires
        pow(4, m) == pow(4, t) * x,
    ensures
        m >= t,
        x == pow(4, m - t),
{
    if m == (0: nat) {
        assert(pow(4, (0: nat)) == 1);
        pow_ge1(t);
        assert(pow(4, t) * x == 1);
        assert(pow(4, t) == 1);
        assert(x == 1);
        assert(t == (0: nat));
        assert(m >= t);
        assert(x == pow(4, m - t));
    } else {
        if t == (0: nat) {
            assert(pow(4, m) == pow(4, (0: nat)) * x);
            assert(x == pow(4, m));
            assert(m >= t);
            assert(x == pow(4, m - t));
        } else {
            assert(pow(4, m) == pow(4, m - (1: nat)) * pow(4, (1: nat)));
            assert(pow(4, t) == pow(4, t - (1: nat)) * pow(4, (1: nat)));
            assert(pow(4, m - (1: nat)) * pow(4, (1: nat)) == (pow(4, t - (1: nat)) * pow(4, (1: nat))) * x);
            assert(pow(4, m - (1: nat)) == pow(4, t - (1: nat)) * x);
            pow4_divide_factor(m - (1: nat), t - (1: nat), x);
            assert(m - (1: nat) >= t - (1: nat));
            assert(x == pow(4, (m - (1: nat)) - (t - (1: nat))));
            assert(m >= t);
            assert(x == pow(4, m - t));
        }
    }
}

// </vc-helpers>

// <vc-spec>
fn if_power_of_four(n: nat) -> (result: bool)
    ensures result <==> (exists|m: nat| n == pow(4, m)),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed numeric literal types and loop invariant */
    let mut x: nat = n;
    let mut t: nat = (0: nat);

    while x > (1: nat) && x % (4: nat) == (0: nat)
        invariant
            x >= (1: nat),
            n == pow(4, t) * x,
        decreases x
    {
        let old_x = x;
        let old_t = t;
        x = old_x / (4: nat);
        t = old_t + (1: nat);
        proof {
            assert(old_x == pow(4, (1: nat)) * x);
            pow_4_add(old_t, (1: nat));
            assert(pow(4, old_t + (1: nat)) == pow(4, old_t) * pow(4, (1: nat)));
            assert(n == pow(4, old_t) * old_x);
            assert(n == pow(4, old_t) * (pow(4, (1: nat)) * x));
            assert(n == (pow(4, old_t) * pow(4, (1: nat))) * x);
            assert(n == pow(4, old_t + (1: nat)) * x);
        }
    }

    let result = x == (1: nat);
    proof {
        if result {
            assert(n == pow(4, t) * x);
            assert(x == (1: nat));
            exists|m: nat| m == t && n == pow(4, m);
        }

        if exists|m: nat| n == pow(4, m) {
            let m = choose|m: nat| n == pow(4, m);
            assert(pow(4, m) == pow(4, t) * x);
            pow4_divide_factor(m, t, x);
            assert(x == pow(4, m - t));
            if m > t {
                assert(m - t > (0: nat));
                assert(x == pow(4, m - t));
                assert(x % (4: nat) == (0: nat));
                assert(x > (1: nat));
            }
            assert(m <= t);
            assert(m == t);
            assert(x == pow(4, (0: nat)));
            assert(x == (1: nat));
        }
    }

    result
}

// </vc-code>

}
fn main() {}