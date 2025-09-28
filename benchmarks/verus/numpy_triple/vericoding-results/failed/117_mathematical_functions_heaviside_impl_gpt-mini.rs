// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): f32 equality symmetry proof */
proof fn f32_eq_sym(a: f32, b: f32)
    ensures a == b ==> b == a
{
    if a == b {
        assert(b == a);
    }
}

// </vc-helpers>

// <vc-spec>
spec fn is_zero(x: f32) -> bool {
    true
}

spec fn is_positive(x: f32) -> bool {
    true
}

spec fn is_negative(x: f32) -> bool {
    true
}

fn heaviside(x1: Vec<f32>, x2: Vec<f32>) -> (result: Vec<f32>)
    requires x1.len() == x2.len(),
    ensures 
        result.len() == x1.len(),
        forall|i: int| 0 <= i < x1.len() ==> {
            (is_negative(x1[i]) ==> result[i] == 0.0f32) &&
            (is_zero(x1[i]) ==> result[i] == x2[i]) &&
            (is_positive(x1[i]) ==> result[i] == 1.0f32) &&
            (result[i] == 0.0f32 || result[i] == 1.0f32 || result[i] == x2[i])
        }
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): use usize loop counter and invariants with int-indexed spec */
    let n: usize = x1.len();
    let mut result: Vec<f32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            result.len() == i,
            forall |j: int| 0 <= j < (i as int) ==> (
                (is_negative(x1[j as usize]) ==> result[j as usize] == 0.0f32) &&
                (is_zero(x1[j as usize]) ==> result[j as usize] == x2[j as usize]) &&
                (is_positive(x1[j as usize]) ==> result[j as usize] == 1.0f32) &&
                (result[j as usize] == 0.0f32 || result[j as usize] == 1.0f32 || result[j as usize] == x2[j as usize])
            ),
        decreases n - i
    {
        let iu: usize = i;
        if is_negative(x1[iu]) {
            result.push(0.0f32);
        } else if is_zero(x1[iu]) {
            result.push(x2[iu]);
        } else if is_positive(x1[iu]) {
            result.push(1.0f32);
        } else {
            result.push(0.0f32);
        }
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}