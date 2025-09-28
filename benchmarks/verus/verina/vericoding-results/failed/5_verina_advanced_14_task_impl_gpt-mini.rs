// <vc-preamble>
use vstd::prelude::*;
use vstd::arithmetic::power::pow;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): proofs about powers of 4 */

proof fn pow_add(m: nat, k: nat)
    ensures pow(4, m + k) == pow(4, m) * pow(4, k)
{
    if m == 0 {
        // pow(4,0) == 1, so pow(4,0 + k) == pow(4,k) == 1 * pow(4,k)
        assert(pow(4, 0 + k) == pow(4, k));
        assert(pow(4, 0) == 1);
        assert(pow(4, k) == 1 * pow(4, k));
    } else {
        pow_add(m - 1, k);
        // pow(4, m + k) == 4 * pow(4, m - 1 + k)
        assert(pow(4, m + k) == 4 * pow(4, m - 1 + k));
        // pow(4, m) == 4 * pow(4, m - 1)
        assert(pow(4, m) == 4 * pow(4, m - 1));
        // by inductive hypothesis pow(4, m - 1 + k) == pow(4, m - 1) * pow(4, k)
        assert(pow(4, m - 1 + k) == pow(4, m - 1) * pow(4, k));
        // combine equalities
        assert(4 * pow(4, m - 1 + k) == 4 * (pow(4, m - 1) * pow(4, k)));
        assert(4 * (pow(4, m - 1) * pow(4, k)) == (4 * pow(4, m - 1)) * pow(4, k));
        assert((4 * pow(4, m - 1)) * pow(4, k) == pow(4, m) * pow(4, k));
        assert(pow(4, m + k) == pow(4, m) * pow(4, k));
    }
}

proof fn pow_ge_one(m: nat)
    ensures pow(4, m) >= 1
{
    if m == 0 {
        assert(pow(4, 0) == 1);
    } else {
        pow_ge_one(m - 1);
        assert(pow(4, m) == 4 * pow(4, m - 1));
        assert(pow(4, m - 1) >= 1);
        assert(4 * pow(4, m - 1) >= 1);
    }
}

proof fn pow_ge_4_if_pos(d: nat)
    requires d > 0
    ensures pow(4, d) >= 4
{
    if d == 1 {
        assert(pow(4, 1) == 4);
    } else {
        pow_ge_4_if_pos(d - 1);
        assert(pow(4, d) == 4 * pow(4, d - 1));
        assert(pow(4, d - 1) >= 4);
        assert(4 * pow(4, d - 1) >= 4);
    }
}

proof fn pow_mono(a: nat, b: nat)
    requires a < b
    ensures pow(4, a) < pow(4, b)
{
    let d = b - a;
    // d > 0
    assert(d > 0);
    // pow(4, b) == pow(4, a) * pow(4, d)
    pow_add(a, d);
    assert(pow(4, b) == pow(4, a) * pow(4, d));
    pow_ge_4_if_pos(d);
    assert(pow(4, d) >= 4);
    assert(pow(4, a) * pow(4, d) > pow(4, a));
}

proof fn pow_div_by_4_if_pos(t: nat)
    requires t > 0
    ensures pow(4, t) % 4 == 0
{
    if t == 1 {
        assert(pow(4, 1) == 4);
        assert(pow(4, 1) % 4 == 0);
    } else {
        // pow(4, t) == 4 * pow(4, t - 1)
        assert(pow(4, t) == 4 * pow(4, t - 1));
        // (4 * A) % 4 == 0
        assert((4 * pow(4, t - 1)) % 4 == 0);
    }
}

// </vc-helpers>

// <vc-spec>
fn if_power_of_four(n: nat) -> (result: bool)
    ensures result <==> (exists|m: nat| n == pow(4, m)),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): determine if n is a power of 4 (fixed exists/forall syntax) */
{
    let mut x: nat = n;
    let mut k: nat = 0;
    while x > 1 && x % 4 == 0
        invariant
            n == x * pow(4, k),
            x >= 0,
            k >= 0,
        decreases x
    {
        x = x / 4;
        k = k + 1;
    }

    if x == 1 {
        proof {
            // From invariant: n == 1 * pow(4, k) == pow(4, k)
            assert(n == x * pow(4, k));
            assert(x == 1);
            assert(n == pow(4, k));
            // witness k
            assert(exists(|m: nat| n == pow(4, m)));
        }
        true
    } else {
        proof {
            // show there is no m with n == pow(4,m)
            forall(|m: nat|) {
                // suppose pow(4,m) == n and derive contradiction
                if pow(4, m) == n {
                    // from invariant n == x * pow(4, k)
                    assert(pow(4, m) == x * pow(4, k));

                    if x == 0 {
                        // pow(4,m) == 0 contradiction because pow >= 1
                        pow_ge_one(m);
                        assert(pow(4, m) >= 1);
                        assert(false);
                    } else {
                        // x > 0
                        if m < k {
                            // then pow(4, m) < pow(4, k)
                            pow_mono(m, k);
                            assert(pow(4, m) < pow(4, k));
                            // but right-hand-side x * pow(4, k) >= pow(4, k)
                            assert(x * pow(4, k) >= pow(4, k));
                            // contradiction with pow(4, m) == x * pow(4, k)
                            assert(false);
                        } else {
                            // m >= k
                            let t: nat = m - k;
                            // pow_add gives pow(4, m) == pow(4, t) * pow(4, k)
                            pow_add(t, k);
                            assert(pow(4, m) == pow(4, t) * pow(4, k));
                            // combine with pow(4,m) == x * pow(4,k) to get x == pow(4,t)
                            assert(x * pow(4, k) == pow(4, t) * pow(4, k));
                            // cancellation: pow(4,k) > 0, so x == pow(4,t)
                            assert(x == pow(4, t));
                            // since x != 1 (we are in else branch) we know t > 0
                            if t == 0 {
                                // then x == 1, contradiction
                                assert(false);
                            } else {
                                // t > 0 implies pow(4,t) divisible by 4, so x % 4 == 0, contradiction
                                pow_div_by_4_if_pos(t);
                                assert(pow(4, t) % 4 == 0);
                                assert(x % 4 == 0);
                                assert(false);
                            }
                        }
                    }
                }
            }
            // thus no m exists with pow(4,m) == n
            assert(!(exists(|m: nat| n == pow(4, m))));
        }
        false
    }
}

// </vc-code>

}
fn main() {}