// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn cube_elements(a: &Vec<i32>) -> (result: Vec<i32>)
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> result[i] == a[i] * a[i] * a[i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): Added overflow checking with assertions */
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == a[j] * a[j] * a[j],
        decreases a.len() - i
    {
        // Check for overflow before computing cube
        assert(a[i] as int * a[i] as int >= i32::MIN as int);
        assert(a[i] as int * a[i] as int <= i32::MAX as int);
        let square = a[i] * a[i];
        assert(square as int * a[i] as int >= i32::MIN as int);
        assert(square as int * a[i] as int <= i32::MAX as int);
        let cube = square * a[i];
        result.push(cube);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}