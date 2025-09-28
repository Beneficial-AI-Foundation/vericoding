// <vc-preamble>
use vstd::prelude::*;

verus! {

struct Complex {

    real: f64,

    imag: f64,
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added proof block to verify the property */
fn loop_invariant_helper(x: &Vec<Complex>, result: &Vec<bool>, i: usize, is_complex_num: bool)
    requires
        i < x.len(),
        result.len() == i,
        forall|j: int| 0 <= j < i ==> result@[j] == (x@[j].imag != 0.0),
        is_complex_num == (x@[i].imag != 0.0),
    ensures
        forall|j: int| 0 <= j < (i + 1) ==> result@.push(is_complex_num)@[j] == (x@[j].imag != 0.0),
{
    proof {
        let new_result = result@.push(is_complex_num);
        assert(forall|j: int| 0 <= j < i ==> new_result[j] == result@[j]);
        assert(new_result[i as int] == is_complex_num);
        assert(is_complex_num == (x@[i as int].imag != 0.0));
        assert(forall|j: int| 0 <= j < (i + 1) ==> new_result[j] == (x@[j].imag != 0.0));
    }
}
// </vc-helpers>

// <vc-spec>
fn is_complex(x: &Vec<Complex>) -> (result: Vec<bool>)
    ensures
        result.len() == x.len(),
        forall|i: int| 0 <= i < x@.len() ==> result@[i] == (x@[i].imag != 0.0),
        forall|i: int| 0 <= i < x@.len() ==> (x@[i].imag == 0.0 ==> result@[i] == false),
        forall|i: int| 0 <= i < x@.len() ==> (x@[i].imag != 0.0 ==> result@[i] == true),
        forall|i: int| 0 <= i < x@.len() ==> (result@[i] == true ==> x@[i].imag != 0.0),
        forall|i: int| 0 <= i < x@.len() ==> (result@[i] == false ==> x@[i].imag == 0.0)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed type errors with i as int indexing */
    let mut result = Vec::new();
    let mut i = 0;
    while i < x.len()
        invariant
            i <= x.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == (x@[j].imag != 0.0),
        decreases x.len() - i
    {
        let is_complex_num = x[i].imag != 0.0;
        proof {
            loop_invariant_helper(x, &result, i, is_complex_num);
        }
        result.push(is_complex_num);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}