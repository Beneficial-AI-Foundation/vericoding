// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn mroot1(n: u32) -> (r: u32)
    requires n >= 0,
    ensures r >= 0 && (r as int) * (r as int) <= n < ((r + 1) as int) * ((r + 1) as int),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Added a bound to the loop condition to resolve overflow and invariant issues. */
    let mut r: u32 = 0;
    while r < 65535 && ((r as u64) + 1) * ((r as u64) + 1) <= (n as u64)
        invariant
            (r as int) * (r as int) <= (n as int),
            (r as int) < 65536,
        decreases (n as int) - (r as int) * (r as int)
    {
        r = r + 1;
    }
    r
}
// </vc-code>

}
fn main() {}