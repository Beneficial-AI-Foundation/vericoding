// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn array_product(a: &Vec<i32>, b: &Vec<i32>) -> (result: Vec<i32>)
    requires a.len() == b.len(),
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> result[i] == a[i] * b[i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): changed invariant and invariant conditions to use view(), added #[auto] triggers, and decreased to spec */
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            result.view().len() == i as int,
            forall|j: int| #![auto] 0 <= j < i ==> result.view()[j] == a.view()[j] * b.view()[j],
        decreases a.view().len() - i
    {
        result.push(a[i] * b[i]);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}