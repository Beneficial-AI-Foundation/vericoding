// <vc-preamble>
use vstd::prelude::*;
use vstd::arithmetic::power::pow;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed parameter types to match i32 inputs */
proof fn left_shift_properties(x: i32, shift: nat) -> (result: i32)
    ensures
        result == x * pow(2, shift),
        shift == 0 ==> result == x,
        x == 0 ==> result == 0,
        x > 0 && shift > 0 ==> result > x,
        x < 0 && shift > 0 ==> result < x
{
    if shift == 0 {
        proof { assert(pow(2, 0) == 1) };
        x
    } else {
        let prev = left_shift_properties(x, (shift - 1) as nat);
        proof { assert(prev == x * pow(2, (shift - 1) as nat)) };
        let current = prev * 2;
        proof { assert(current == x * pow(2, shift)) };
        proof { 
            if x > 0 && shift > 0 {
                assert(pow(2, shift) > 1);
                assert(x * pow(2, shift) > x * 1);
            }
            if x < 0 && shift > 0 {
                assert(pow(2, shift) > 1);
                assert(x * pow(2, shift) < x);
            }
        };
        current
    }
}
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
/* code modified by LLM (iteration 5): Fixed type casting for vector indexing */
{
    let mut result: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < x1.len()
        invariant
            0 <= i <= x1.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == x1[j] * pow(2, x2[j] as nat),
            forall|j: int| 0 <= j < i && x2[j] == 0 ==> result[j] == x1[j],
            forall|j: int| 0 <= j < i && x1[j] == 0 ==> result[j] == 0,
            forall|j: int| 0 <= j < i && x1[j] > 0 && x2[j] > 0 ==> result[j] > x1[j],
            forall|j: int| 0 <= j < i && x1[j] < 0 && x2[j] > 0 ==> result[j] < x1[j]
    {
        proof {
            let ghost_shifted = left_shift_properties(x1.index(i) as i32, x2.index(i) as nat);
            assert(ghost_shifted == x1.index(i) as i32 * pow(2, x2.index(i) as nat));
        }
        let shifted_value = x1[i] * (1 << x2[i]);
        result.push(shifted_value);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}