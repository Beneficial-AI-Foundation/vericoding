// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Renamed `div_euclid` to `rem_euclid` to align with expected usage, and implemented Euclidean remainder definition. Fixed type mismatch in remainder check. */
fn rem_euclid(a: int, b: int) -> (result: int)
    requires b != 0,
             b > 0
    ensures (result == a % b + if a % b < 0 { b } else { 0})
{
    let remainder: int = a % b;
    if remainder < 0 {
        remainder + b
    } else {
        remainder
    }
}
// </vc-helpers>

// <vc-spec>
fn ifftshift(x: Vec<f32>) -> (result: Vec<f32>)
    requires x.len() > 0,
    ensures 
        result.len() == x.len(),
        forall|i: int| 0 <= i < x@.len() ==> 
            result[i] == x[((i + (x@.len() as int) / 2) % (x@.len() as int)) as int]
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Addressed type mismatches by casting `j` to `int` before passing to `rem_euclid` and converting `original_idx_ghost` to `nat` for `x@.index`. Also fixed the cast of `original_index_ghost` to `usize` by ensuring `original_index_ghost` is non-negative and within `usize` bounds, then cast as `nat` and then to `usize` for `Vec` indexing. */
{
    let len = x.len();
    let mut result = Vec::new();
    result.reserve(len as usize);

    let ghost shift: int = (len as int) / 2;

    let mut i: usize = 0;
    while i < len
        invariant
            0 <= i && i <= len,
            result.len() == i,
            result.capacity() == len,
            forall|j: int| 0 <= j < i ==> {
                let ghost original_idx_ghost: int = rem_euclid(j + shift, len as int);
                result@.index(j as nat) == x@.index(original_idx_ghost as nat)
            },
        decreases (len - i)
    {
        let ghost original_index_ghost: int = rem_euclid((i as int) + shift, len as int); // Original index in the input `x`
        assert(0 <= original_index_ghost);
        assert(original_index_ghost < len as int);
        let original_index = original_index_ghost as nat;
        result.push(x[original_index as usize]);
        i = i + 1;
    }
    
    result
}
// </vc-code>


}
fn main() {}