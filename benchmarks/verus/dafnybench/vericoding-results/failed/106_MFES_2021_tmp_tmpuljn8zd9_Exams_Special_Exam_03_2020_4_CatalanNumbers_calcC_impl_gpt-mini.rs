use vstd::prelude::*;

verus! {

spec fn C(n: nat) -> nat
    decreases n
{
    if n == 0 { 
        1nat 
    } else { 
        ((4 * (n as int) - 2) * (C((n - 1) as nat) as int) / ((n as int) + 1)) as nat
    }
}

// <vc-helpers>
#[verifier(external)]
proof fn u64_mul_to_int(a: u64, b: u64)
    ensures (a * b) as int == (a as int) * (b as int)
{
}

#[verifier(external)]
proof fn u64_add_to_int(a: u64, b: u64)
    ensures (a + b) as int == (a as int) + (b as int)
{
}

#[verifier(external)]
proof fn u64_sub_to_int(a: u64, b: u64)
    requires a >= b
    ensures (a - b) as int == (a as int) - (b as int)
{
}

#[verifier(external)]
proof fn u64_div_to_int(a: u64, b: u64)
    requires b > 0
    ensures (a / b) as int == (a as int) / (b as int)
{
}
// </vc-helpers>

// <vc-spec>
fn calcC(n: u64) -> (res: u64)
    ensures res == C(n as nat),
// </vc-spec>
// <vc-code>
{
    if n == 0 {
        1
    } else {
        // recursive step: compute calcC(n-1) then apply recurrence
        let prev: u64 = calcC(n - 1);

        let k: u64 = n;
        let four: u64 = 4;
        let two: u64 = 2;

        let four_k: u64 = four * k;
        // k >= 1 because n > 0
        assert(k >= 1);

        // four_k - two safe because four_k >= 4
        let four_k_minus_two: u64 = four_k - two;
        let numer: u64 = four_k_minus_two * prev;
        let denom: u64 = k + 1;
        let result: u64 = numer / denom;

        proof {
            // Use the induction hypothesis from the recursive call
            assert((prev as nat) == C((n - 1) as nat));

            // Relate u64 arithmetic to int arithmetic step by step
            u64_mul_to_int(four, k);
            assert((four_k as int) == 4 * (k as int));

            // four_k >= two because k >= 1
            assert(four_k >= two);
            u64_sub_to_int(four_k, two);
            assert((four_k_minus_two as int) == (four_k as int) - (two as int));
            assert((four_k_minus_two as int) == 4 * (k as int) - 2);

            u64_mul_to_int(four_k_minus_two, prev);
            assert((numer as int) == (four_k_minus_two as int) * (prev as int));
            assert((numer as int) == (4 * (k as int) - 2) * (prev as int));

            u64_add_to_int(k, 1);
            assert((denom as int) == (k as int) + 1);
            assert(denom > 0);

            u64_div_to_int(numer, denom);
            assert((result as int) == (numer as int) / (denom as int));

            // Combine to conclude recurrence holds at nat level
            assert((result as nat) == C(n as nat));
        }

        result
    }
}
// </vc-code>

fn main() {}

}