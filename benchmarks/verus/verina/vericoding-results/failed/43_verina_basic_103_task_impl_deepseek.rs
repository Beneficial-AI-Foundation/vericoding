// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed invariant for index 4 and added safety bounds */
fn update_elements_helper(a: &Vec<i32>, i: usize) -> (result: i32)
    requires 0 <= i < a.len(),
    ensures
        result == (if i == 4 { a[i] + 3 } else if i == 7 { 516 } else { a[i] }),
{
    if i == 4 {
        a[i] + 3
    } else if i == 7 {
        516
    } else {
        a[i]
    }
}
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
/* code modified by LLM (iteration 5): Fixed while loop with proper bounds checking */
{
    let mut result = Vec::with_capacity(a.len());
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i && j != 4 && j != 7 ==> result[j] == a[j],
            i > 4 ==> result[4] == a[4] + 3,
            i > 7 ==> result[7] == 516,
        decreases a.len() - i,
    {
        let val: i32 = update_elements_helper(a, i);
        result.push(val);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}