// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): renamed to `cube_i32_vspec` to indicate it is a pure function for ghost code, and not for `exec` */
fn cube_i32_vspec(x: i32) -> (result: i32)
    requires
        (x as i64) * (x as i64) * (x as i64) >= i32::MIN as i64,
        (x as i64) * (x as i64) * (x as i64) <= i32::MAX as i64,
    ensures
        result == x * x * x,
{
    x * x * x
}
// </vc-helpers>

// <vc-spec>
fn cube_elements(a: &Vec<i32>) -> (result: Vec<i32>)
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> result[i] == a[i] * a[i] * a[i],
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): The mismatch type error happens because trying to use `a[i]` as an `int` directly within the `assert` statement's multiplication. `a[i]` is an `i32` and `i` is a `usize`, so `a[i]` returns an `i32`. However, for the multiplication in specification context, Verus prefers `int` types to reason about potential overflows more generally. To fix, you have to cast `x` to `int`, instead of to `i64` */
{
    let mut result = Vec::new();
    let mut i = 0;
    while i < a.len()
        invariant
            0 <= i,
            i <= a.len(),
            result.len() == i,
            // All elements processed so far satisfy the cubed property, and no overflow occurred.
            forall|j: int| 0 <= j < i ==> result[j] == cube_i32_vspec(a[j]),
            // For elements that will be processed, ensure no overflow during cubing.
            forall|j: int| i <= j < a.len() ==> 
                (a[j] as int) * (a[j] as int) * (a[j] as int) >= i32::MIN as int &&
                (a[j] as int) * (a[j] as int) * (a[j] as int) <= i32::MAX as int,
        decreases a.len() - i
    {
        // Prove the preconditions for cube_i32_vspec by casting `a[i]` to `int`
        proof {
            assert((a[i] as int) * (a[i] as int) * (a[i] as int) >= i32::MIN as int);
            assert((a[i] as int) * (a[i] as int) * (a[i] as int) <= i32::MAX as int);
        }
        let cubed_val = a[i] * a[i] * a[i]; // Perform the actual calculations in exec
        result.push(cubed_val);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}