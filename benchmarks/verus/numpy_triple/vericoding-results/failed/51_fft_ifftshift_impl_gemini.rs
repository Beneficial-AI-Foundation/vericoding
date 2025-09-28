// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
{
    let n = x.len() as int;
    let p = n / 2;
    let mut result = Vec::new();
    let mut i = 0;
    while i < n
        invariant
            x.len() as int == n,
            p == n / 2,
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == x@[((j + p) % n) as int],
        decreases n - i
    {
        let src_idx = ((i + p) % n) as usize;
        result.push(x[src_idx]);
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}