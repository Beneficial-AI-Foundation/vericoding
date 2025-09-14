// <vc-preamble>
use vstd::prelude::*;

verus!{

spec fn triangle(n: nat) -> (result: nat)
    decreases n
{
    if n == 0 {
        0
    } else {
        n + triangle((n - 1) as nat)
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Removed non-compiling helper function template. */
// </vc-helpers>

// <vc-spec>
fn tail_triangle(n: u32, idx: u32, sum: &mut u32)

    requires
        idx <= n,
        *old(sum) == triangle(idx as nat),
        triangle(n as nat) < 0x1_0000_0000,

    ensures
        *sum == triangle(n as nat),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Added decreases clause and implemented the recursive logic. */
{
    decreases (n - idx);

    if idx == n {
        // Base case: *sum already holds triangle(n)
    } else {
        let next_idx = idx + 1;

        // Prove the invariant for the recursive call
        proof {
            assert(*sum == triangle(idx as nat)); // From precondition or previous iteration
            assert(idx as nat <= n as nat);

            // This assertion relies on the property of triangle numbers
            // triangle(k) + (k+1) = triangle(k+1)
            assert(triangle(idx as nat) + next_idx as nat == triangle(next_idx as nat));
        }

        *sum = *sum + next_idx;

        tail_triangle(n, next_idx, sum); // Recursive call
    }
}
// </vc-code>

}
fn main() {}