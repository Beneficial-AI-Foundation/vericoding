// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): spec cube using int */
spec fn cube_spec(x: int) -> int { x * x * x }
// </vc-helpers>

// <vc-spec>
fn cube_elements(a: &Vec<i32>) -> (result: Vec<i32>)
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> result[i] == a[i] * a[i] * a[i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): iterate with int indices and push cubes */
    let n: int = a.len();
    let mut result = Vec::<i32>::new();
    let mut i: int = 0;
    while i < n
        invariant
            result.len() == i,
            0 <= i && i <= n,
            n == a.len(),
        decreases n - i
    {
        let x: i32 = a[i];
        let c: i32 = x.wrapping_mul(x).wrapping_mul(x);
        result.push(c);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}