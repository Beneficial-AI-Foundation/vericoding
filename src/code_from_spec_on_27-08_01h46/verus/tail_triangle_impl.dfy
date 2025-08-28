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

proof fn triangle_accumulation_lemma(idx: nat, n: nat)
    requires
        idx <= n,
    ensures
        triangle(idx) + (triangle(n) - triangle(idx)) == triangle(n),
    decreases n
{
}

proof fn triangle_step_lemma(idx: nat)
    requires
        idx > 0,
    ensures
        triangle(idx) == triangle((idx - 1) as nat) + idx,
    decreases idx
{
}

proof fn triangle_bounds_lemma(n: nat)
    requires
        triangle(n) < 0x1_0000_0000,
        n > 0,
    ensures
        triangle((n - 1) as nat) < 0x1_0000_0000,
{
    triangle_is_monotonic((n - 1) as nat, n);
}

proof fn addition_bounds_lemma(sum: u32, idx: u32, n: u32)
    requires
        triangle(n as nat) < 0x1_0000_0000,
        sum == triangle((idx - 1) as nat),
        idx <= n,
        idx > 0,
    ensures
        sum + idx <= 0xFFFF_FFFF,
{
    triangle_step_lemma(idx as nat);
    assert(triangle(idx as nat) == triangle((idx - 1) as nat) + idx as nat);
    triangle_is_monotonic(idx as nat, n as nat);
    assert(triangle(idx as nat) <= triangle(n as nat));
    assert(sum + idx == triangle(idx as nat));
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
{
    let mut current_idx = idx;
    while current_idx < n
        invariant
            current_idx <= n,
            *sum == triangle(current_idx as nat),
            triangle(n as nat) < 0x1_0000_0000,
        decreases n - current_idx
    {
        current_idx += 1;
        proof {
            triangle_step_lemma(current_idx as nat);
            addition_bounds_lemma(*sum, current_idx, n);
        }
        *sum = *sum + current_idx;
    }
}
// </vc-code>

}

fn main() {}