// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn numpy_mod(x1: Vec<i8>, x2: Vec<i8>) -> (result: Vec<i8>)
    requires 
        x1.len() == x2.len(),
        forall|i: int| 0 <= i < x2.len() ==> x2[i] != 0,
    ensures
        result.len() == x1.len(),
        forall|i: int| 0 <= i < result.len() ==> 
            #[trigger] result[i] == x1[i] % x2[i],
        forall|i: int| 0 <= i < result.len() ==> {
            let r = #[trigger] result[i];
            let a = x1[i];
            let b = x2[i];
            /* Basic remainder property: a = floor_div(a, b) * b + r */
            a == (a / b) * b + r &&
            /* Result has same sign as divisor (when divisor is non-zero) */
            (b > 0 ==> r >= 0 && r < b) &&
            (b < 0 ==> r <= 0 && r > b)
        }
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Adding #[trigger] to `result_vec[j]` to fix quantifier trigger issue. */
{
    let mut result_vec = Vec::new();
    let mut i = 0;
    while i < x1.len()
        invariant
            0 <= i <= x1.len(),
            result_vec.len() == i,
            forall|j: int| 0 <= j < i ==> {
                let r: i8 = #[trigger] result_vec[j];
                let a = x1[j];
                let b = x2[j];
                a == (a / b) * b + r &&
                (b > 0 ==> r >= 0 && r < b) &&
                (b < 0 ==> r <= 0 && r > b)
            }
        ,
        decreases x1.len() - i
    {
        let val1 = x1[i];
        let val2 = x2[i];
        let res_val = val1 % val2;
        result_vec.push(res_val);
        i = i + 1;
    }
    result_vec
}
// </vc-code>


}
fn main() {}