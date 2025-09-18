// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn hermevander(x: Vec<f64>, deg: usize) -> (result: Vec<Vec<f64>>)
    requires deg >= 0,
    ensures
        result.len() == x.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i].len() == deg + 1,
        forall|i: int| 0 <= i < result.len() ==> result[i][0] == 1.0,
        deg > 0 ==> forall|i: int| 0 <= i < result.len() ==> result[i][1] == x[i],
// </vc-spec>
// <vc-code>
{
/* code modified by LLM (iteration 2): Fixed loop range from 1..=deg to 1..(deg+1) to resolve compilation error with RangeInclusive */
    let mut result = Vec::new();
    for i in 0..x.len() {
        let mut row = Vec::new();
        let mut val = 1.0;
        row.push(1.0);
        for k in 1..(deg + 1) {
            val = val * x[i];
            row.push(val);
        }
        result.push(row);
    }
    result
}
// </vc-code>

}
fn main() {}