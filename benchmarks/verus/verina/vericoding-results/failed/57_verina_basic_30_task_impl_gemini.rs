// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): no helpers needed */
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
/* code modified by LLM (iteration 5): added assertion for non-zero divisor and used assert_seqs_equal to prove forall invariant after push */
{
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            a.len() == b.len(),
            forall|k: int| 0 <= k < b.len() ==> b@[k] != 0,
            0 <= i <= a.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == a@[j] % b@[j],
        decreases a.len() - i
    {
        assert(b[i] != 0);
        let val = a[i] % b[i];

        let ghost old_result_view = result@;
        result.push(val);
        assert_seqs_equal!(result@, old_result_view.push(val));

        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}