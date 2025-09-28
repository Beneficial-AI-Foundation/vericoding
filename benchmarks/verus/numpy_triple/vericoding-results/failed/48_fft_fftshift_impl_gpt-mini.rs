// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): convert int modulo to usize with range proof */
spec fn mod_to_usize(a: int, n: int) -> (result: usize)
    requires
        n > 0,
    ensures
        (result as int) == a % n,
        0 <= (result as int),
        (result as int) < n,
{
    let r: int = a % n;
    r as usize
}
// </vc-helpers>

// <vc-spec>
fn fftshift(x: Vec<f32>) -> (result: Vec<f32>)
    ensures
        result.len() == x.len(),
        forall|i: int| 0 <= i < result.len() as int ==> 
            result[i as int] == x[((i + (x.len() as int) - (x.len() as int) / 2) % (x.len() as int)) as int]
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): implement fftshift using mod_to_usize and loop invariants */
    let n_usize: usize = x.len();
    let shift: usize = n_usize / 2;
    let mut result: Vec<f32> = Vec::new();
    result.reserve(n_usize);
    let mut i: usize = 0;
    while i < n_usize
        invariant
            0 <= i as int,
            i as int <= n_usize as int,
            result.len() as int == i as int,
            forall|j: int| 0 <= j < i as int ==> 
                result[j as usize] == x[((j + n_usize as int - shift as int) % n_usize as int) as usize],
        decreases n_usize - i
    {
        let idx_usize: usize = (i + n_usize - shift) % n_usize;
        result.push(x[idx_usize]);
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}