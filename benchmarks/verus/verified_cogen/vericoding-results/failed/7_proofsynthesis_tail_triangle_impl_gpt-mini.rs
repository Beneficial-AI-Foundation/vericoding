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
/* helper modified by LLM (iteration 5): triangle_add_one proves triangle(n+1)=triangle(n)+(n+1) */
proof fn triangle_add_one(n: nat)
    ensures
        triangle(n + 1) == triangle(n) + (n + 1),
    decreases
        n
{
    if n == 0 {
        assert(triangle(0) == 0);
        assert(triangle(1) == 1);
        assert(triangle(1) == triangle(0) + 1);
    } else {
        triangle_add_one((n - 1) as nat);
        assert(triangle(n) == triangle((n - 1) as nat) + n);
        assert(triangle(n + 1) == triangle(n) + (n + 1));
    }
}

/* helper modified by LLM (iteration 5): triangle_monotone proves triangle is nondecreasing */
proof fn triangle_monotone(a: nat, b: nat)
    requires
        a <= b,
    ensures
        triangle(a) <= triangle(b),
    decreases
        b - a
{
    if a == b {
        assert(triangle(a) == triangle(b));
    } else {
        let bm1: nat = (b - 1) as nat;
        triangle_add_one(bm1);
        triangle_monotone(a, bm1);
        assert(triangle(b) == triangle(bm1) + b);
        assert(triangle(bm1) >= triangle(a));
        assert(triangle(b) >= triangle(a));
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
{
    /* code modified by LLM (iteration 5): iterate from idx to n updating sum using ghost triangle and safe casts */
    let mut i: u32 = idx;
    while i < n
        invariant
            i <= n,
            *sum == triangle(i as nat),
        decreases
            n - i
    {
        let next: u32 = i + 1;
        let ghost new_sum_nat: nat = triangle(next as nat);
        proof {
            triangle_add_one(i as nat);
            triangle_monotone(next as nat, n as nat);
            assert(new_sum_nat == triangle(next as nat));
            assert(new_sum_nat <= triangle(n as nat));
            assert(triangle(n as nat) < 0x1_0000_0000);
            assert(new_sum_nat < 0x1_0000_0000);
        }
        *sum = new_sum_nat as u32;
        i = next;
    }
}
// </vc-code>

}
fn main() {}