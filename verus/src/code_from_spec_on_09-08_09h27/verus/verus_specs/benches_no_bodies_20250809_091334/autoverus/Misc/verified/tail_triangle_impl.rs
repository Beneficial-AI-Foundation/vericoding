//This is an example from Verus tutorial Chpt 4.2
//This is a rather complicated example: a inductive proof function is introduced to help prove that *sum will not overflow

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
    if i == j {
        // Base case: triangle(i) == triangle(j)
    } else {
        // Inductive case: i < j
        triangle_is_monotonic(i, (j - 1) as nat);
        // We know triangle(i) <= triangle(j-1)
        // Since triangle(j) = j + triangle(j-1), we have triangle(j-1) <= triangle(j)
        // Therefore triangle(i) <= triangle(j)
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
        decreases
            n - current_idx,
    {
        current_idx = current_idx + 1;
        *sum = *sum + current_idx;
    }
}
}