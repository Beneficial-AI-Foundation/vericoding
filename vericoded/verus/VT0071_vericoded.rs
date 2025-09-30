// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn lemma_len_reflexive(a: &Vec<f64>)
    ensures
        a.len() == a.len(),
{
}

// </vc-helpers>

// <vc-spec>
fn size(a: &Vec<f64>) -> (result: usize)
    ensures result == a.len()
// </vc-spec>
// <vc-code>
{
    let r = a.len();
    r
}
// </vc-code>

}
fn main() {}