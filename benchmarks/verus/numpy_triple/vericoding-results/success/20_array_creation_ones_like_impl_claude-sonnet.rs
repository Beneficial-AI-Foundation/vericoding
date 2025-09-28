// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn ones_like<T>(a: &Vec<T>) -> (result: Vec<i32>)
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == 1,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): added invariant about upper bound to ensure postcondition */
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            result.len() == i,
            i <= a.len(),
            forall|j: int| 0 <= j < result.len() ==> result[j] == 1,
        decreases a.len() - i
    {
        result.push(1);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}