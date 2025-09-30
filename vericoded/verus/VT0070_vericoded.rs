// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn lemma_len_reflexive<T>(a: &Vec<T>)
    ensures
        a.len() == a.len(),
{
}

// </vc-helpers>

// <vc-spec>
fn shape<T>(a: &Vec<T>) -> (result: usize)
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