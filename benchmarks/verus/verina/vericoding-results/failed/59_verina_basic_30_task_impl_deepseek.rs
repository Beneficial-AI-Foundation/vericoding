// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Remove nat helper, use usize directly */
fn abs(x: i32) -> i32 { if x >= 0 { x } else { -x } }
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
/* code modified by LLM (iteration 5): Use usize loop counter with proper type handling */
{
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == a@[j] % b@[j],
        decreases a.len() - i
    {
        let elem_a = a[i];
        let elem_b = b[i];
        assert(b[i] != 0);
        let mod_result = elem_a % elem_b;
        result.push(mod_result);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}