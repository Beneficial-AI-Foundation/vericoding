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
    /* code modified by LLM (iteration 2): added decreases clause to while loop */
    let mut result = Vec::new();
    let mut i = 0;
    while i < val.len()
        invariant
            0 <= i <= val.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j as int] == val[j as int].1,
            forall|j: int| 0 <= j < i ==> (val[j as int].1 == 0.0 ==> result[j as int] == 0.0),
            forall|j: int| 0 <= j < i ==> (val[j as int].0 != 0.0 || val[j as int].1 != 0.0 ==> result[j as int] == val[j as int].1),
        decreases val.len() - i
    {
        let (_, imag_part) = val[i];
        result.push(imag_part);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}