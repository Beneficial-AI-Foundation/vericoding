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
/* helper modified by LLM (iteration 5): Fixed requires clause formatting and proof logic */
proof fn sum_triangle_ind(n: nat, idx: nat, sum: nat)
    decreases n - idx
    requires
        idx <= n,
        sum == triangle(idx)
    ensures
        sum + (triangle(n) - triangle(idx)) == triangle(n)
{
    if n > idx {
        let next_idx = idx + 1;
        let next_sum = sum + next_idx;
        sum_triangle_ind(n, next_idx, next_sum);
    }
}
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
/* code modified by LLM (iteration 5): Fixed verification with proper proof structure */
{
    if idx < n {
        let next_idx: u32 = idx + 1;
        let current_sum: u32 = *sum;
        proof {
            sum_triangle_ind(n as nat, idx as nat, current_sum as nat);
        }
        let new_sum: u32 = current_sum + next_idx;
        *sum = new_sum;
        tail_triangle(n, next_idx, sum);
    } else {
        assert(*sum == triangle(n as nat));
    }
}
// </vc-code>

}
fn main() {}