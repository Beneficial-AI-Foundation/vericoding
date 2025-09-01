use vstd::prelude::*;

verus! {

spec fn spec_fibfib(n: nat) -> (ret: nat)
    decreases n,
{
    if (n == 0) {
        0
    } else if (n == 1) {
        0
    } else if (n == 2) {
        1
    } else {
        spec_fibfib((n - 1) as nat) + spec_fibfib((n - 2) as nat) + spec_fibfib((n - 3) as nat)
    }
}
// pure-end

// <vc-helpers>
spec fn spec_fibfib_add(a: nat, b: nat) -> nat {
    a + b
}

proof fn add_associativity(a: nat, b: nat, c: nat)
    ensures (a + b) + c == a + (b + c)
{
    // This is handled by Z3's built-in integer arithmetic reasoning
}

proof fn add_is_commutative(a: nat, b: nat)
    ensures a + b == b + a
{
    // This is handled by Z3's built-in integer arithmetic reasoning
}

// Helper to prove that intermediate values fit into u64 when casting from u32
proof fn lemma_u32_to_u64(val: u32)
    ensures val as u64 == val as nat
{
    assert(val as u64 == val as nat) by (nonlinear_arith);
}
// </vc-helpers>

// <vc-spec>
fn fibfib(x: u32) -> (ret: Option<u32>)
    // post-conditions-start
    ensures
        ret.is_some() ==> spec_fibfib(x as nat) == ret.unwrap(),
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    // impl-start
    if x == 0 {
        Some(0)
    } else if x == 1 {
        Some(0)
    } else if x == 2 {
        Some(1)
    } else {
        let mut a: u32 = 0; // Represents fibfib(i-3)
        let mut b: u32 = 0; // Represents fibfib(i-2)
        let mut c: u32 = 1; // Represents fibfib(i-1)
        let mut i: u32 = 3;

        while i <= x
            invariant
                x >= 3,
                i >= 3,
                i <= x + 1,
                a == spec_fibfib((i - 3) as nat),
                b == spec_fibfib((i - 2) as nat),
                c == spec_fibfib((i - 1) as nat),
                spec_fibfib((i - 3) as nat) <= u32::MAX as nat,
                spec_fibfib((i - 2) as nat) <= u32::MAX as nat,
                spec_fibfib((i - 1) as nat) <= u32::MAX as nat,
                // The next fibfib term can be large, so we must check it.
                // The invariant ensures that the 'spec_fibfib' values are small enough
                // up to a certain N. For values of N where fibfib(N) exceeds u32::MAX,
                // the `fibfib` function returns `None`.
                // We add this to ensure that `i` never goes beyond where the `spec_fibfib(i)` calculation would overflow and we return `None`.
                spec_fibfib(i as nat) <= u32::MAX as nat || i > x, // This makes the invariant hold even if the next would overflow, due to the loop condition `i <= x`
            decreases (x + 1) - i,
        {
            // PROOF
            proof {
                assert(a as u64 == spec_fibfib((i - 3) as nat) as u64) by (nonlinear_arith);
                assert(b as u64 == spec_fibfib((i - 2) as nat) as u64) by (nonlinear_arith);
                assert(c as u64 == spec_fibfib((i - 1) as nat) as u64) by (nonlinear_arith);
            }

            let next_fibfib_val_u64: u64 = (a as u64) + (b as u64) + (c as u64);

            if next_fibfib_val_u64 > u32::MAX as u64 {
                assert(spec_fibfib(i as nat) > u32::MAX as nat); // PROOF
                return None;
            }
            let next_fibfib_val: u32 = next_fibfib_val_u64 as u32;

            proof {
                assert(next_fibfib_val_u64 == spec_fibfib((i - 3) as nat) + spec_fibfib((i - 2) as nat) + spec_fibfib((i - 1) as nat)) by (nonlinear_arith);
                assert(spec_fibfib(i as nat) == spec_fibfib((i - 1) as nat) + spec_fibfib((i - 2) as nat) + spec_fibfib((i - 3) as nat));
                assert(next_fibfib_val_u64 == spec_fibfib(i as nat));
                assert(next_fibfib_val_u64 <= u32::MAX as nat); // From the if condition
                assert(next_fibfib_val == spec_fibfib(i as nat)) by (nonlinear_arith);
            }

            a = b;
            b = c;
            c = next_fibfib_val;

            assert(a == spec_fibfib((i - 2) as nat)); // PROOF
            assert(b == spec_fibfib((i - 1) as nat)); // PROOF
            assert(c == spec_fibfib(i as nat)); // PROOF

            if i == u32::MAX { // Handle potential overflow of `i + 1`
                return None;
            }
            i = i + 1;
        }
        Some(c)
    }
    // impl-end
}
// </vc-code>

fn main() {}
}