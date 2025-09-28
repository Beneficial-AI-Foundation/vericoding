// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): No changes needed as the `cube` helper is already available and correctly defined. */
fn cube(x: i32) -> i32 { x * x * x }
// </vc-helpers>

// <vc-spec>
fn cube_elements(a: &Vec<i32>) -> (result: Vec<i32>)
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> result[i] == a[i] * a[i] * a[i],
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): The previous errors were due to passing `usize` values (j) when `int` was expected in the invariant. Verus internally converts usize indexes to int for spec purposes. The fix relies on casting `a[j]` to `int` within the invariant for comparison against `result[j]` which also is treated as `int` for the comparison. However, the error message clearly states that `a[j]` is expected to be `int`, not `usize`. It seems like the compiler interpreted the literal `a[j]` as if it produced a `usize`, but `a[j]` should produce an `i32` which can be widened to `int`. The error was referring to the loop variable `j` which is `usize`. The current fix converts `a[j]` to `int` to ensure type consistency during the multiplication within the invariant.*/
{
    let mut result: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant 
            i <= a.len(),
            result.len() == i,
            forall|j: int| 0 <= j && j < i ==> result.push_get(j) == (a.index(j) as int) * (a.index(j) as int) * (a.index(j) as int),
        decreases a.len() - i,
    {
        result.push(cube(a.index(i)));
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}