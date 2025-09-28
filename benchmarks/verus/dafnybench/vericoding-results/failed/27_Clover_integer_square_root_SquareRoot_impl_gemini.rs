// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn square_root(n: u32) -> (r: u32)
  ensures r * r <= n < (r + 1) * (r + 1)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Switched to spec (`nat`) arithmetic in the `while` condition to resolve the overflow verification error. */
    let mut r: u64 = 0;
    while r < 65536 && ((r + 1) as nat) * ((r + 1) as nat) <= (n as nat)
        invariant
            (r as nat) * (r as nat) <= (n as nat),
            r <= 65536,
        decreases (n as nat) - (r as nat) * (r as nat)
    {
        r = r + 1;
    }
    r as u32
}
// </vc-code>

}
fn main() {}