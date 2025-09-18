// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed return variable name */
fn safe_cube(x: i32) -> (cube_result: i32)
    requires
        -1290 <= x <= 1290,
    ensures
        cube_result == x * x * x,
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
{
    /* code modified by LLM (iteration 5): fixed type error by using int conversion for indexing */
    let mut result = Vec::new();
    let mut i = 0;
    while i < a.len()
        invariant
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == a[j] * a[j] * a[j],
        decreases a.len() - i
    {
        proof {
            assert(-1290 <= a[i as int] <= 1290);
        }
        let cube = safe_cube(a[i]);
        result.push(cube);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}