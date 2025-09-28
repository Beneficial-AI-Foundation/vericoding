use vstd::prelude::*;

verus! {

// <vc-helpers>
// no helpers needed
// </vc-helpers>

// <vc-spec>
fn sum(n: u32) -> (s: u32)
    requires n >= 0
    ensures s == n * (n + 1) / 2
// </vc-spec>
// <vc-code>
{
    let s = (n * (n + 1)) / 2;
    s
}
// </vc-code>

fn main() {}

}