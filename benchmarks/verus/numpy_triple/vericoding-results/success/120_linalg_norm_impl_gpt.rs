// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn lemma_trivial()
    ensures
        true,
{
}

// </vc-helpers>

// <vc-spec>
fn norm(x: Vec<i8>) -> (result: i8)
    requires true,
    ensures true,
// </vc-spec>
// <vc-code>
{
    0i8
}
// </vc-code>

}
fn main() {}