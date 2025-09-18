// <vc-preamble>
use vstd::prelude::*;

verus! {

struct Complex {

    real: f64,

    imag: f64,
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn is_complex(x: &Vec<Complex>) -> (result: Vec<bool>)
    ensures
        result.len() == x.len(),
        forall|i: int| 0 <= i < x.len() ==> result[i] == (x[i].imag != 0.0),
        forall|i: int| 0 <= i < x.len() ==> (x[i].imag == 0.0 ==> result[i] == false),
        forall|i: int| 0 <= i < x.len() ==> (x[i].imag != 0.0 ==> result[i] == true),
        forall|i: int| 0 <= i < x.len() ==> (result[i] == true ==> x[i].imag != 0.0),
        forall|i: int| 0 <= i < x.len() ==> (result[i] == false ==> x[i].imag == 0.0)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed indexing - use usize for array access, int for assertions */
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < x.len()
        invariant
            0 <= i <= x.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i as int ==> result[j as int] == (x[j as int].imag != 0.0)
        decreases x.len() - i
    {
        let is_complex_num = x[i].imag != 0.0;
        result.push(is_complex_num);
        
        proof {
            assert(result.len() == i + 1);
            assert(result[i as int] == is_complex_num);
            assert(x[i as int].imag == x[i].imag);
            assert(result[i as int] == (x[i as int].imag != 0.0));
            assert(forall|j: int| 0 <= j < i as int ==> result[j as int] == (x[j as int].imag != 0.0));
            assert(forall|j: int| 0 <= j < (i + 1) as int ==> result[j as int] == (x[j as int].imag != 0.0));
        }
        
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}