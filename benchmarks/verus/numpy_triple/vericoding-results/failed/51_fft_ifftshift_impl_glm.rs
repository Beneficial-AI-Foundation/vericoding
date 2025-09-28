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
    let half = n / 2;
    let mut result = Vec::new();
    for i in 0..n {
        let idx = (i + half) % n;
        result.push(x[idx as usize]);
    }
    result
}
// </vc-code>


}
fn main() {}