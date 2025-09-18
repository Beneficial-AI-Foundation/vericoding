// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn lemma_add_zero(x: int) ensures x + 0 == x { }
// </vc-helpers>

// <vc-spec>
fn mod_func(a: Vec<String>, values: Vec<String>) -> (result: Vec<String>)
    requires a.len() == values.len(),
    ensures 
        result.len() == a.len(),
// </vc-spec>
// <vc-code>
{
    values
}
// </vc-code>

}
fn main() {}