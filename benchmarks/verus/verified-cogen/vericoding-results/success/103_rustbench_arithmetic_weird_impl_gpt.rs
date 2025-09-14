// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn choose_small() -> (r: i32)
    ensures
        r < 10
{
    0
}
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn arithmetic_weird() -> (result: i32)
    ensures
        result < 10
// </vc-spec>
// <vc-code>
{
    let r = choose_small();
    r
}
// </vc-code>

}
fn main() {}