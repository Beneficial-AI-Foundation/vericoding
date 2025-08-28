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

// <vc-helpers>
proof fn triangle_additive(n: nat, m: nat)
    requires
        n <= m,
    ensures
        if m > n {
            triangle(m) == triangle(n) + (m - n) + triangle((m - n - 1) as nat)
        } else {
            triangle(m) == triangle(n)
        },
    decreases m
{
    if n < m {
        triangle_additive(n, (m - 1) as nat);
    }
}
// </vc-helpers>

// <vc-spec>
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
// </vc-spec>

// <vc-code>
fn tail_triangle(n: u32, idx: u32, sum: &mut u32)
    requires
        idx <= n,
        *old(sum) == triangle(idx as nat),
        triangle(n as nat) < 0x1_0000_0000,
    ensures
        *sum == triangle(n as nat),
    decreases n - idx
{
    if idx < n {
        *sum = *sum + (n - idx) as u32;
        tail_triangle(n, idx + 1, sum);
    }
}
// </vc-code>

}

fn main() {}