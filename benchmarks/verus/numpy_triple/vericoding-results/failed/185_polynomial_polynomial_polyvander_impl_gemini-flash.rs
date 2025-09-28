// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): The `pow_f32` function now uses `u32` for `exp` to avoid casting issues with `nat` in executable code, ensuring better compatibility with Verus's type system while maintaining the intended mathematical behavior. */
fn pow_f32(base: f32, exp: u32) -> (ret: f32)
    ensures
        exp == 0 ==> ret == 1.0f32,
        exp == 1 ==> ret == base,
        exp > 1 ==> ret == base * pow_f32(base, exp - 1),
{
    if exp == 0 {
        1.0f32
    } else if exp == 1 {
        base
    } else {
        base * pow_f32(base, exp - 1)
    }
}
// </vc-helpers>

// <vc-spec>
fn polyvander(x: Vec<f32>, deg: usize) -> (result: Vec<Vec<f32>>)
    requires x.len() > 0,
    ensures
        result.len() == x.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i].len() == deg + 1,
        forall|i: int| 0 <= i < result.len() ==> result[i][0] == 1.0f32,
        deg > 0 ==> forall|i: int| 0 <= i < result.len() ==> result[i][1] == x[i]
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): The `polyvander` function now uses `u32` for loop counters and indices where `nat` was previously used, to align with the updated `pow_f32` helper function and resolve type-related compilation errors. This ensures proper casting and type compatibility for executable code while maintaining verification properties. */
{
    let mut result: Vec<Vec<f32>> = Vec::new();
    let x_len = x.len();
    let x_spec = x@;

    while result.len() < x_len
        invariant
            result.len() <= x_len,
            x_spec.len() == x_len,
            forall|i: int| 0 <= i < result.len() ==> result[i].len() == deg + 1,
            forall|i: int| 0 <= i < result.len() ==> result[i][0] == 1.0f32,
            deg > 0 ==> forall|i: int| 0 <= i < result.len() ==> result[i][1] == x_spec[i],
            forall|i: int, j: int| 0 <= i < result.len() && 0 <= j < result[i].len() ==> result[i][j] == pow_f32(x_spec[i], j as u32)
    {
        let mut row: Vec<f32> = Vec::new();
        let current_x = x@[result.len()];
        let mut j: u32 = 0;

        while j <= deg as u32
            invariant
                j <= (deg as u32) + 1,
                row.len() == j as usize,
                forall|k: u32| 0 <= k && k < j ==> row[k as int] == pow_f32(current_x, k),
        {
            row.push(pow_f32(current_x, j));
            j = j + 1;
        }
        result.push(row);
    }
    result
}
// </vc-code>


}
fn main() {}