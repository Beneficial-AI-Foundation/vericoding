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
{
    /* code modified by LLM (iteration 5): fix ghost variable syntax error */
    if x.len() == 0 {
        return Vec::new();
    }
    
    let mut result = Vec::with_capacity(x.len());
    let n_ghost: Ghost<int> = Ghost(x.len() as int);
    let shift_ghost: Ghost<int> = Ghost(n_ghost@ / 2);
    
    let mut i = 0;
    while i < x.len()
        invariant
            i <= x.len(),
            result.len() == i,
            n_ghost@ == x.len() as int,
            shift_ghost@ == n_ghost@ / 2,
            forall|j: int| 0 <= j < i ==>
                result[j] == x[((j + n_ghost@ - shift_ghost@) % n_ghost@) as int]
    {
        let src_idx = ((i + x.len() - (x.len() / 2)) % x.len()) as usize;
        result.push(x[src_idx]);
        i += 1;
    }
    
    result
}
// </vc-code>


}
fn main() {}