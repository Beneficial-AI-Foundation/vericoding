// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): convert usize to int */
fn usz_to_int(u: usize) -> int {
    u as int
}

/* helper modified by LLM (iteration 5): helper to create an empty Vec<bool> */
fn make_bool_vec() -> Vec<bool> {
    Vec::new()
}
// </vc-helpers>

// <vc-spec>
fn not_equal(x1: Vec<String>, x2: Vec<String>) -> (result: Vec<bool>)
    requires x1.len() == x2.len(),
    ensures 
        result.len() == x1.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == (x1[i] != x2[i])
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): use usize->int conversion helper and build res */
    let mut res: Vec<bool> = make_bool_vec();
    let mut i: int = usz_to_int(0);
    while i < usz_to_int(x1.len())
        invariant
            usz_to_int(0) <= i,
            i <= usz_to_int(x1.len()),
            usz_to_int(res.len()) == i,
            forall|j: int| 0 <= j && j < i ==> res[j] == (x1[j] != x2[j]),
        decreases usz_to_int(x1.len()) - i
    {
        let b: bool = x1[i] != x2[i];
        res.push(b);
        i = i + usz_to_int(1);
    }
    res
}
// </vc-code>

}
fn main() {}