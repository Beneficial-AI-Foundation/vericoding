// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Return value is now named as required for ensures clause. */
fn positive_arithmetic_right_shift(x: i32, k: i32) -> (result: i32)
    requires
        x >= 0,
        k >= 0,
    ensures
        result == x / (1i32 << k),
    decreases k
{
    if k == 0 {
        result = x
    } else {
        result = positive_arithmetic_right_shift(x / 2, k - 1)
    }
}
// </vc-helpers>

// <vc-spec>
fn right_shift(x1: Vec<i32>, x2: Vec<i32>) -> (result: Vec<i32>)
    requires 
        x1.len() == x2.len(),
        forall|i: int| 0 <= i < x2.len() ==> x2[i] >= 0,
    ensures
        result.len() == x1.len(),
        forall|i: int| 0 <= i < result.len() ==> {
            &&& (x1[i] >= 0 ==> result[i] == x1[i] / (1i32 << x2[i]))
            &&& (x1[i] < 0 ==> result[i] == x1[i] >> x2[i])
            &&& (x2[i] == 0 ==> result[i] == x1[i])
            &&& (x1[i] > 0 ==> result[i] >= 0)
            &&& (x1[i] < 0 ==> result[i] <= 0)
            &&& (x1[i] == 0 ==> result[i] == 0)
        }
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): No changes, implementation is correct after helper fix. */
{
    let mut result = Vec::<i32>::new();
    let mut index = 0;
    while index < x1.len()
        invariant
            index <= x1.len(),
            result@.len() == index,
            forall|j: int| 0 <= j < index ==> {
                &&& (x1@[j] >= 0 ==> result@[j] == x1@[j] / (1i32 << x2@[j]))
                &&& (x1@[j] < 0 ==> result@[j] == x1@[j] >> x2@[j])
                &&& (x2@[j] == 0 ==> result@[j] == x1@[j])
                &&& (x1@[j] > 0 ==> result@[j] >= 0)
                &&& (x1@[j] < 0 ==> result@[j] <= 0)
                &&& (x1@[j] == 0 ==> result@[j] == 0)
            },
        decreases x1.len() - index,
    {
        if x1[index] >= 0 {
            let val = positive_arithmetic_right_shift(x1[index], x2[index]);
            result.push(val);
        } else {
            let val = x1[index] >> x2[index];
            result.push(val);
        }
        index += 1;
    }
    result
}
// </vc-code>

}
fn main() {}