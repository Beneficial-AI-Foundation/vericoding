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
/* code modified by LLM (iteration 5): Fixed compilation error with missing comma in assert and added type constraints for vec push operations */
{
    let mut result_vec = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i as int <= a.len() as int,
            result_vec.len() == i,
            result_vec.len() <= a.len(),
            forall|j: int| 0 <= j < i as int ==> result_vec[j] == a[j] % b[j],
        decreases a.len() - i,
    {
        proof {
            assert(0 <= i as int && i as int < a.len() as int);
            assert(0 <= i as int && i as int < b.len() as int);
            let b_val: i32 = b[i as int];
            assert(b_val != 0);
        }
        result_vec.push(a[i as int] % b[i as int]);
        i = i + 1;
    }
    result_vec
}
// </vc-code>

}
fn main() {}