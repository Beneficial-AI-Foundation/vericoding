// <vc-preamble>
use vstd::prelude::*;

verus! {

struct Complex {

    real: f64,

    imag: f64,
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): lemma to establish postcondition properties */
proof fn establish_postcondition(x: &Vec<Complex>, result: &Vec<bool>)
    requires
        result.len() == x.len(),
        forall|i: int| 0 <= i < x.len() ==> result[i] == (x[i].imag != 0.0)
    ensures
        forall|i: int| 0 <= i < x.len() ==> (x[i].imag == 0.0 ==> result[i] == false),
        forall|i: int| 0 <= i < x.len() ==> (x[i].imag != 0.0 ==> result[i] == true),
        forall|i: int| 0 <= i < x.len() ==> (result[i] == true ==> x[i].imag != 0.0),
        forall|i: int| 0 <= i < x.len() ==> (result[i] == false ==> x[i].imag == 0.0)
{
}
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
    /* code modified by LLM (iteration 5): use helper lemma and update invariant to establish all properties */
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < x.len()
        invariant
            i <= x.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i as int ==> result[j as int] == (x[j as int].imag != 0.0),
            forall|j: int| 0 <= j < i as int ==> (x[j as int].imag == 0.0 ==> result[j as int] == false),
            forall|j: int| 0 <= j < i as int ==> (x[j as int].imag != 0.0 ==> result[j as int] == true),
            forall|j: int| 0 <= j < i as int ==> (result[j as int] == true ==> x[j as int].imag != 0.0),
            forall|j: int| 0 <= j < i as int ==> (result[j as int] == false ==> x[j as int].imag == 0.0)
        decreases x.len() - i
    {
        let is_complex_num = x[i].imag != 0.0;
        result.push(is_complex_num);
        proof {
            assert(result[i as int] == (x[i as int].imag != 0.0));
            assert(x[i as int].imag == 0.0 ==> result[i as int] == false);
            assert(x[i as int].imag != 0.0 ==> result[i as int] == true);
            assert(result[i as int] == true ==> x[i as int].imag != 0.0);
            assert(result[i as int] == false ==> x[i as int].imag == 0.0);
        }
        i += 1;
    }
    proof {
        establish_postcondition(x, &result);
    }
    result
}
// </vc-code>

}
fn main() {}