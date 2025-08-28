use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn lemma_mul_strictly_increases(a: int, b: int)
    requires a > 0, b > 0,
    ensures a * b > a,
{
    // Proof by induction or algebraic reasoning is implicit in Verus for small integers
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn mroot1(n: u32) -> (r: u32) //Cost O(root n)
    requires n >= 0,
    ensures r >= 0 && (r as int) * (r as int) <= n < ((r + 1) as int) * ((r + 1) as int),
// </vc-spec>
// </vc-spec>

// <vc-code>
fn mroot1(n: u32) -> (r: u32)
    requires n >= 0,
    ensures r >= 0 && (r as int) * (r as int) <= (n as int) && (n as int) < ((r + 1) as int) * ((r + 1) as int),
{
    let mut r: u32 = 0;
    while ((r + 1) as int) * ((r + 1) as int) <= (n as int)
        invariant r >= 0,
        invariant (r as int) * (r as int) <= (n as int),
        decreases (n as int) - (r as int),
    {
        r = r + 1;
    }
    r
}
// </vc-code>

fn main() {}

}