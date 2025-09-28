// <vc-preamble>
use vstd::prelude::*;
use vstd::arithmetic::power::pow;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn left_shift(x1: Vec<i32>, x2: Vec<i32>) -> (result: Vec<i32>)
    requires
        x1.len() == x2.len(),
        forall|i: int| 0 <= i < x2.len() ==> x2[i] >= 0,
    ensures
        result.len() == x1.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == x1[i] * pow(2, x2[i] as nat),
        forall|i: int| 0 <= i < result.len() && x2[i] == 0 ==> result[i] == x1[i],
        forall|i: int| 0 <= i < result.len() && x1[i] == 0 ==> result[i] == 0,
        forall|i: int| 0 <= i < result.len() && x1[i] > 0 && x2[i] > 0 ==> result[i] > x1[i],
        forall|i: int| 0 <= i < result.len() && x1[i] < 0 && x2[i] > 0 ==> result[i] < x1[i],
// </vc-spec>
// <vc-code>
{
    let mut i: int = 0;
    let mut result_vec: Vec<i32> = Vec::new();
    while i < x1.len()
        invariant
            0 <= i <= x1.len(),
            result_vec.len() == i,
            forall|j: int| 0 <= j < i ==> result_vec[j] == x1[j] * pow(2, x2[j] as nat),
        decreases x1.len() - i
    {
        let v = x1[i] * pow(2, x2[i] as nat);
        result_vec.push(v);
        i += 1;
    }
    result_vec
}
// </vc-code>

}
fn main() {}