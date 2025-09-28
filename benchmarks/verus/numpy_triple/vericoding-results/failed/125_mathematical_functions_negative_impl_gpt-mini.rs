// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): negate an i8 safely using int arithmetic, avoiding overflow */
fn neg_i8(x: i8) -> (result: i8)
    ensures
        result as int == -(x as int),
{
    let tmp: int = -(x as int);
    tmp as i8
}
// </vc-helpers>

// <vc-spec>
fn numpy_negative(x: Vec<i8>) -> (result: Vec<i8>)
    ensures
        result.len() == x.len(),
        forall|i: int| 0 <= i < x.len() ==> result[i] as int == -(x[i] as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): build result vector by negating each element using helper */
    let mut res: Vec<i8> = Vec::new();
    let mut i: usize = 0;
    while i < x.len()
        invariant
            i <= x.len(),
            res.len() == i,
            forall|j: int| 0 <= j < i as int ==> res[j] as int == -(x[j] as int),
        decreases x.len() - i
    {
        let xi: i8 = x[i];
        let yi: i8 = neg_i8(xi);
        res.push(yi);
        i = i + 1;
    }
    res
}
// </vc-code>


}
fn main() {}