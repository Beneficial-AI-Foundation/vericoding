// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn power(x: nat, y: nat) -> nat
    decreases y
{
    if y == 0 { 1 } else { x * power(x, (y - 1) as nat) }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): [kept from previous iteration] */
proof fn lemma_power_of_one(y: nat)
    ensures power(1, y) == 1
    decreases y
{
    if y > 0 {
        lemma_power_of_one((y - 1) as nat);
        assert(power(1, y) == 1 * power(1, (y - 1) as nat));
    }
}

/* helper modified by LLM (iteration 5): [kept from previous iteration] */
proof fn lemma_power_is_positive(x: nat, y: nat)
    requires x > 0
    ensures power(x, y) > 0
    decreases y
{
    if y > 0 {
        lemma_power_is_positive(x, (y - 1) as nat);
    } else {
        assert(power(x, y) == 1);
    }
}

/* helper modified by LLM (iteration 5): [kept from previous iteration] */
proof fn lemma_power_strictly_monotonic(x: nat, y1: nat, y2: nat)
    requires
        x > 1,
        y1 < y2,
    ensures power(x, y1) < power(x, y2)
    decreases y2 - y1
{
    if y2 == y1 + 1 {
        lemma_power_is_positive(x, y1);
        // By definition, power(x, y2) == x * power(x, y1).
        // From requires x > 1 and lemma_power_is_positive(x, y1), we know power(x, y1) > 0.
        // Verus can deduce that for a > 1 and b > 0, we have b < a * b.
        // Thus power(x, y1) < x * power(x, y1) == power(x, y2).
    } else {
        lemma_power_strictly_monotonic(x, y1, (y2 - 1) as nat);
        lemma_power_strictly_monotonic(x, (y2 - 1) as nat, y2);
    }
}
// </vc-helpers>

// <vc-spec>
fn is_simple_power(x: u8, n: i8) -> (ans: bool)
    requires x > 0
    ensures ans <==> exists|y: nat| n as int == power(x as nat, y) as int
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): [Added missing comma in while loop invariant block.] */
{
    let x_nat = x as nat;
    let n_int = n as int;

    if n_int <= 0 {
        proof {
            assert forall|y: nat| n_int != power(x_nat, y) as int by {
                lemma_power_is_positive(x_nat, y);
            }
        }
        return false;
    }

    if n_int == 1 {
        proof {
            assert(power(x_nat, 0) == 1);
        }
        return true;
    }

    if x_nat == 1 {
        proof {
            assert forall|y: nat| power(x_nat, y) == 1 by {
                lemma_power_of_one(y);
            }
            assert(n_int != 1);
        }
        return false;
    }

    let mut p: int = 1;
    let ghost mut k: nat = 0;
    let x_int = x as int;

    while p < n_int
        invariant
            x_nat > 1,
            n_int > 1,
            p == power(x_nat, k) as int,
            forall|j: nat| j < k ==> power(x_nat, j) as int < n_int,
        decreases n_int - p
    {
        proof {
            lemma_power_is_positive(x_nat, k);
        }
        p = p * x_int;
        k = k + 1;
    }

    let result = p == n_int;
    if result {
        assert(exists|y: nat| n_int == power(x_nat, y) as int);
    } else {
        proof {
            assert(p > n_int);
            assert forall|y: nat| n_int != power(x_nat, y) as int by {
                if y < k {
                    assert(power(x_nat, y) as int < n_int);
                } else { // y >= k
                    if y > k {
                        lemma_power_strictly_monotonic(x_nat, k, y);
                    }
                    assert(power(x_nat, y) as int >= p);
                    assert(n_int < p <= power(x_nat, y) as int);
                }
            }
        }
    }
    result
}
// </vc-code>


}

fn main() {}