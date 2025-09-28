// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): no helper needed */
// </vc-helpers>

// <vc-spec>
fn update_elements(a: &Vec<i32>) -> (result: Vec<i32>)
    requires a.len() >= 8,
    ensures
        result[4] == a[4] + 3,
        result[7] == 516,
        forall|i: int| 0 <= i < a.len() && i != 4 && i != 7 ==> result[i] == a[i],
        result.len() == a.len(),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): add assertions to prove bounds and prevent arithmetic overflow */
{
    let mut result = Vec::with_capacity(a.len());
    for i in 0..a.len() {
        result.push(a[i]);
    }
    assert(4 < result.view().len() && 4 >= 0);
    assert(a.view()[4] <= 2147483644);
    result[4] = a[4] + 3;
    assert(7 < result.view().len() && 7 >= 0);
    result[7] = 516;
    result
}
// </vc-code>

}
fn main() {}