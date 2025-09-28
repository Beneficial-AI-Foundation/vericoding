// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn imag(val: Vec<(f64, f64)>) -> (result: Vec<f64>)
    ensures
        result.len() == val.len(),
        forall|i: int| 0 <= i < val.len() ==> result[i as int] == val[i as int].1,
        forall|i: int| 0 <= i < val.len() ==> (val[i as int].1 == 0.0 ==> result[i as int] == 0.0),
        forall|i: int| 0 <= i < val.len() ==> (val[i as int].0 != 0.0 || val[i as int].1 != 0.0 ==> result[i as int] == val[i as int].1),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): added decreases clause to the while loop */
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < val.len()
        invariant
            i <= val.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i as int ==> result[j] == val[j].1,
        decreases val.len() - i
    {
        result.push(val[i].1);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}