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
/* code modified by LLM (iteration 5): Fix Vec indexing for `a.get_spec` and `b.get_spec` */
{
    let mut result = Vec::new();
    let len = a.len();
    let mut i: usize = 0;

    while i < len
        invariant
            0 <= i as int && i as int <= len as int,
            result.len() == i,
            forall|j: int| 0 <= j && j < i as int ==> result@[j] == a@[j] * b@[j],
    {
        result.push(a[i] * b[i]);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}