// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added parentheses to fix operator precedence */
fn isqrt(n: u32) -> (r: u32)
    ensures
        (r as u64) * (r as u64) <= (n as u64),
        (n as u64) < ((r as u64) + 1) * ((r as u64) + 1),
        r <= 65535,
{
    let mut r: u32 = 0;
    while r < 65535 && ((r as u64) + 1) * ((r as u64) + 1) <= (n as u64)
        invariant
            (r as u64) * (r as u64) <= (n as u64),
            r <= 65535,
        decreases 65536u32 - r
    {
        r = r + 1;
    }
    r
}
// </vc-helpers>

// <vc-spec>
fn q(x: u32, y: u32) -> (z: u32)
    requires y - x > 2
    ensures x < z*z < y
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): implemented a correct linear search for z */
    let r = isqrt(x);
    let mut z = r;

    if z < 65535 {
        z = z + 1;
    }

    let mut z_sq = (z as u64) * (z as u64);

    while z_sq <= (x as u64)
        invariant
            z <= 65535,
            z > 0,
            ((z - 1) as u64) * ((z - 1) as u64) <= (x as u64),
            z_sq == (z as u64) * (z as u64),
        decreases 65536u32 - z
    {
        z = z + 1;
        z_sq = (z as u64) * (z as u64);
    }

    z
}
// </vc-code>

}
fn main() {}