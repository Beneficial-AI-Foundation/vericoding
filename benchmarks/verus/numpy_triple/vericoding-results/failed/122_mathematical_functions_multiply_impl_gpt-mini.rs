// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): simple i8 multiplication helper */
fn mul_i8(a: i8, b: i8) -> i8 {
    a * b
}
// </vc-helpers>

// <vc-spec>
fn multiply(x1: Vec<i8>, x2: Vec<i8>) -> (result: Vec<i8>)
    requires x1.len() == x2.len(),
    ensures 
        result.len() == x1.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] as int == (x1[i] as int) * (x2[i] as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): use int indices and proper casting for Vec indexing */
    let mut res: Vec<i8> = Vec::new();
    let mut i: int = 0;
    while i < (x1.len() as int)
        invariant
            0 <= i,
            i <= (x1.len() as int),
            res.len() == (i as usize),
            forall|j: int| 0 <= j && j < i ==> res[(j as usize)] as int == (x1[(j as usize)] as int) * (x2[(j as usize)] as int),
        decreases (x1.len() as int) - i
    {
        let a = x1[i as usize];
        let b = x2[i as usize];
        let p = mul_i8(a, b);
        res.push(p);
        proof {
            assert(res.len() == (i as usize) + 1);
            assert(res[i as usize] as int == (x1[i as usize] as int) * (x2[i as usize] as int));
        }
        i = i + 1;
    }
    res
}
// </vc-code>


}
fn main() {}