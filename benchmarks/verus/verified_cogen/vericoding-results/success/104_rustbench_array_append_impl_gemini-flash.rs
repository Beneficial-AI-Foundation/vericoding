// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn array_append(a: Vec<i32>, b: i32) -> (result: Vec<i32>)
    ensures
        result.len() == a.len() + 1,
        forall|i: int| #![auto] 0 <= i && i < result.len() ==> result[i] == (if i < a.len() { a[i] } else { b }),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): added decreases clause to loop */
{
    let mut result = Vec::new();
    let mut i = 0;
    while i < a.len()
        invariant
            0 <= i && i <= a.len(),
            result.len() == i,
            forall|j: int| 0 <= j && j < i ==> result[j] == a[j],
        decreases a.len() - i
    {
        result.push(a[i]);
        i = i + 1;
    }
    result.push(b);
    result
}
// </vc-code>

}
fn main() {}