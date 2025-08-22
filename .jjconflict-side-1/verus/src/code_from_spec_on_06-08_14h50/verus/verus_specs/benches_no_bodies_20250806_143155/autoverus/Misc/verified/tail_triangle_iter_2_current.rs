use vstd::prelude::*;
fn main() {}

verus!{
     
spec fn triangle(n: nat) -> nat
    decreases n
{
    if n == 0 {
        0
    } else {
        n + triangle((n - 1) as nat)
    }
}

proof fn triangle_is_monotonic(i: nat, j: nat)
    requires
        i <= j,
    ensures
        triangle(i) <= triangle(j),
    decreases j
{
    if i < j {
        triangle_is_monotonic(i, (j - 1) as nat);
    }
}

fn tail_triangle(n: u32, idx: u32, sum: &mut u32)
    requires
        idx <= n,
        *old(sum) == triangle(idx as nat),
        triangle(n as nat) < 0x1_0000_0000,
    ensures
        *sum == triangle(n as nat),
{
    let mut current_idx = idx;
    while current_idx < n
        invariant
            current_idx <= n,
            *sum == triangle(current_idx as nat),
            triangle(n as nat) < 0x1_0000_0000,
        /* code modified by LLM (iteration 1): added decreases clause for loop termination */
        decreases n - current_idx
    {
        current_idx = current_idx + 1;
        *sum = *sum + current_idx;
        proof {
            assert(*sum == triangle((current_idx - 1) as nat) + current_idx as nat);
            assert(triangle(current_idx as nat) == current_idx as nat + triangle((current_idx - 1) as nat));
        }
    }
}
}