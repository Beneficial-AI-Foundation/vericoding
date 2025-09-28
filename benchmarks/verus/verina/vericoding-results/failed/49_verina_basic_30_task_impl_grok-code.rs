// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn element_wise_modulo(a: &Vec<i32>, b: &Vec<i32>) -> (result: Vec<i32>)
    requires
        a.len() == b.len(),
        a.len() > 0,
        forall|i: int| 0 <= i < b.len() ==> b[i] != 0,
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == a[i] % b[i],
// </vc-spec>
// <vc-code>
{
/* code modified by LLM (iteration 5): using usize for loop index to avoid using ghost types in executable code */
    let mut result = Vec::<i32>::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i as int <= a@.len(),
            a@.len() == b@.len(),
            result@.len() == i as int,
            forall|j: int| 0 <= j < i as int ==> #[trigger] result@[j] == a@[j] % b@[j],
        decreases a@.len() - i
    {
        result.push(a[i] % b[i]);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}