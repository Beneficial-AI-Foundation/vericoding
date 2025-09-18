// <vc-preamble>
use vstd::prelude::*;

verus! {

struct Complex {

    real: f64,

    imag: f64,
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed sequence indexing syntax in forall */
proof fn loop_invariant_preserved(x: &Vec<Complex>, i: int, result: Vec<bool>, new_val: bool)
    requires
        0 <= i < x.len(),
        result.len() == i,
        forall|j: int| 0 <= j < i ==> result[j] == (x[j].imag == 0.0),
        new_val == (x[i].imag == 0.0)
    ensures
        forall|j: int| 0 <= j <= i ==> (if j < i then result[j] else new_val) == (x[j].imag == 0.0)
{
    assert forall|j: int| 0 <= j <= i implies (if j < i then result[j] else new_val) == (x[j].imag == 0.0) by {
        if j < i {
            assert(result[j] == (x[j].imag == 0.0));
        } else {
            assert(j == i);
            assert(new_val == (x[i].imag == 0.0));
        }
    };
}
// </vc-helpers>

// <vc-spec>
fn isreal(x: &Vec<Complex>) -> (result: Vec<bool>)
    ensures
        result.len() == x.len(),
        forall|i: int| 0 <= i < x.len() ==> result[i] == (x[i].imag == 0.0),
        forall|i: int| 0 <= i < x.len() ==> (x[i].imag == 0.0 ==> result[i] == true),
        forall|i: int| 0 <= i < x.len() ==> (x[i].imag != 0.0 ==> result[i] == false),
        forall|i: int| 0 <= i < x.len() ==> (result[i] == true ==> x[i].imag == 0.0),
        forall|i: int| 0 <= i < x.len() ==> (result[i] == false ==> x[i].imag != 0.0),
        forall|i: int| 0 <= i < x.len() ==> (result[i] == true ==> x[i].real == x[i].real),
        forall|i: int| 0 <= i < x.len() ==> result[i] == !(x[i].imag != 0.0),
        forall|i: int| 0 <= i < x.len() ==> (result[i] == true <==> x[i].imag == 0.0),
// </vc-spec>
// <vc-code>
{
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < x.len()
        invariant
            0 <= i <= x.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == (x[j].imag == 0.0),
        decreases x.len() - i
    {
        let new_val = x[i].imag == 0.0;
        proof {
            loop_invariant_preserved(x, i, result, new_val);
        }
        result.push(new_val);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}