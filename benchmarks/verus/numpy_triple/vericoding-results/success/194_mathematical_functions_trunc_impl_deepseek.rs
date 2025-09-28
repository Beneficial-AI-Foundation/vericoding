// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn int_abs(x: int) -> int {
    if x >= 0 { x } else { -x }
}
// </vc-preamble>

// <vc-helpers>

proof fn trunc_sign_preservation_lemma(x: i8, result: i8)
    requires
        result == x,
    ensures
        (x > 0 ==> result >= 0) &&
        (x < 0 ==> result <= 0) &&
        (x == 0 ==> result == 0) &&
        int_abs(result as int) <= int_abs(x as int)
{
}

proof fn trunc_abs_property_lemma(x: i8, result: i8)
    requires
        result == x,
    ensures
        int_abs(result as int) <= int_abs(x as int)
{
}

// </vc-helpers>

// <vc-spec>
fn numpy_trunc(x: Vec<i8>) -> (result: Vec<i8>)
    ensures
        result.len() == x.len(),
        forall|i: int| 0 <= i < result.len() ==> #[trigger] result[i] == x[i],
        forall|i: int| 0 <= i < result.len() ==> {
            /* Sign preservation */
            (x[i] > 0 ==> result[i] >= 0) &&
            (x[i] < 0 ==> result[i] <= 0) &&
            (x[i] == 0 ==> result[i] == 0)
        },
        forall|i: int| 0 <= i < result.len() ==> {
            /* Truncation moves towards zero (abs property) */
            int_abs(result[i] as int) <= int_abs(x[i] as int)
        }
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): Add explicit Vec type annotation */
    let mut result_vec: Vec<i8> = Vec::new();
    let mut i: usize = 0;
    
    while i < x.len()
        invariant
            i <= x.len(),
            result_vec.len() == i,
            forall|j: int| 0 <= j < i ==> #[trigger] result_vec[j] == x[j],
            forall|j: int| 0 <= j < i ==> {
                (x[j] > 0 ==> result_vec[j] >= 0) &&
                (x[j] < 0 ==> result_vec[j] <= 0) &&
                (x[j] == 0 ==> result_vec[j] == 0)
            },
            forall|j: int| 0 <= j < i ==> int_abs(result_vec[j] as int) <= int_abs(x[j] as int)
        decreases x.len() - i
    {
        let element = x[i];
        result_vec.push(element);
        proof {
            trunc_sign_preservation_lemma(element, element);
            trunc_abs_property_lemma(element, element);
        }
        i += 1;
    }
    
    result_vec
}
// </vc-code>


}
fn main() {}