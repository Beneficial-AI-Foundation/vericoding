// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn remove_front(a: &Vec<i32>) -> (result: Vec<i32>)
    requires a.len() > 0,
    ensures
        a.len() > 0,
        result.len() == a.len() - 1,
        forall|i: int| 0 <= i < result.len() ==> result[i] == a[i + 1],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): added a decreases clause to the while loop to prove termination */
    let mut result = Vec::new();
    let mut i: usize = 1;
    while i < a.len()
        invariant
            a.len() > 0,
            1 <= i <= a.len(),
            result.len() == i - 1,
            forall|j: int| 0 <= j < result.len() ==> result@[j] == a@[j + 1],
        decreases a.len() - i,
    {
        result.push(a[i]);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}