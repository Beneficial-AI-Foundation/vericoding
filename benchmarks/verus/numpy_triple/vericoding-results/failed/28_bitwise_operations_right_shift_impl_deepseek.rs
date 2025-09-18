// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed type annotations and improved proof logic */
proof fn nonnegative_shift_preserves_sign(x: i32, shift: i32)
    requires
        x >= 0,
        shift >= 0
    ensures
        x / (1i32 << shift) >= 0
{
    assert(1i32 << shift >= 1);
    assert(x / (1i32 << shift) >= 0);
}

proof fn negative_shift_preserves_sign(x: i32, shift: i32)
    requires
        x < 0,
        shift >= 0
    ensures
        x >> shift <= 0
{
    assert(x >> shift <= 0);
}

proof fn zero_shift_identity(x: i32, shift: i32)
    requires
        shift == 0
    ensures
        x / (1i32 << shift) == x,
        x >> shift == x
{
    assert(1i32 << 0 == 1);
    assert(x / 1 == x);
    assert(x >> 0 == x);
}

proof fn zero_input_zero_output(x: i32, shift: i32)
    requires
        x == 0,
        shift >= 0
    ensures
        x / (1i32 << shift) == 0,
        x >> shift == 0
{
    assert(0i32 / (1i32 << shift) == 0);
    assert(0i32 >> shift == 0);
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
/* code modified by LLM (iteration 5): Added explicit type annotations to literals */
{
    let mut result: Vec<i32> = Vec::new();
    let n = x1.len();
    let mut i = 0;
    while i < n
        invariant
            0 <= i <= n,
            result.len() == i,
            forall|j: int| 0 <= j < i ==> {
                &&& (x1[j] >= 0 ==> result@[j] == x1[j] / (1i32 << x2[j]))
                &&& (x1[j] < 0 ==> result@[j] == x1[j] >> x2[j])
                &&& (x2[j] == 0 ==> result@[j] == x1[j])
                &&& (x1[j] > 0 ==> result@[j] >= 0)
                &&& (x1[j] < 0 ==> result@[j] <= 0)
                &&& (x1[j] == 0 ==> result@[j] == 0)
            }
        decreases n - i
    {
        assert(i < x1.len());
        assert(i < x2.len());
        let x_val = x1[i];
        let shift_val = x2[i];
        proof {
            if x_val >= 0 {
                nonnegative_shift_preserves_sign(x_val, shift_val);
            }
            if x_val < 0 {
                negative_shift_preserves_sign(x_val, shift_val);
            }
            if shift_val == 0 {
                zero_shift_identity(x_val, shift_val);
            }
            if x_val == 0 {
                zero_input_zero_output(x_val, shift_val);
            }
        }
        let shifted = if x_val >= 0 {
            x_val / (1i32 << shift_val)
        } else {
            x_val >> shift_val
        };
        result.push(shifted);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}