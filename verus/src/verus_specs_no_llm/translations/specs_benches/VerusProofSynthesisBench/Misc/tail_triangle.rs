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
// pure-end

proof fn triangle_is_monotonic(i: nat, j: nat)
    // pre-conditions-start
    requires
        i <= j,
    // pre-conditions-end
    // post-conditions-start
    ensures
        triangle(i) <= triangle(j),
    decreases j
    // post-conditions-end
{
    // impl-start
    if i < j {
        triangle_is_monotonic(i, (j - 1) as nat);
    }
    // impl-end
}
// pure-end

fn tail_triangle(n: u32, idx: u32, sum: &mut u32)
    // pre-conditions-start
    requires
        idx <= n,
        *old(sum) == triangle(idx as nat),
        triangle(n as nat) < 0x1_0000_0000,
    // pre-conditions-end
    // post-conditions-start
    ensures
        *sum == triangle(n as nat),
    // post-conditions-end
{
    // TODO: Remove this comment and implement the function body
}
}

fn main() {}