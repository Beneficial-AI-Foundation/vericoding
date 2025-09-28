// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn fftshift(x: Vec<f32>) -> (result: Vec<f32>)
    ensures
        result.len() == x.len(),
        forall|i: int| 0 <= i < result.len() as int ==> 
            result[i as int] == x[((i + (x.len() as int) - (x.len() as int) / 2) % (x.len() as int)) as int]
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Remove capacity() check, it's not supported */
{
    let n = x.len();
    if n == 0 {
        return Vec::new();
    }

    let mut result: Vec<f32> = Vec::with_capacity(n);
    let mid_usize = n / 2;

    let mut i: usize = 0;
    while i < n
        invariant
            result.len() == i,
            i <= n,
            result.capacity() == n,
            forall|j: int| 0 <= j < i as int ==> 
                result[j as int] == x[((j + n as int - mid_usize as int) % n as int) as int],
    {
        let original_index: usize;
        if i < mid_usize {
            original_index = i + mid_usize;
        } else {
            original_index = i - mid_usize;
        }
        result.push(x[original_index]);
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}