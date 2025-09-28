// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): simple element-wise i8 subtraction (no wrapping helper) */
fn sub_elem(a: i8, b: i8) -> i8 {
    a - b
}
// </vc-helpers>

// <vc-spec>
fn subtract(x1: Vec<i8>, x2: Vec<i8>) -> (result: Vec<i8>)
    requires x1.len() == x2.len(),
    ensures 
        result.len() == x1.len(),
        forall|i: int| 0 <= i < result.len() ==> result@[i] == x1@[i] - x2@[i],
        /* Sanity check: subtracting zero preserves the original value */
        forall|i: int| 0 <= i < result.len() && x2@[i] == 0 ==> result@[i] == x1@[i],
        /* Sanity check: subtracting a value from itself yields zero */
        forall|i: int| 0 <= i < result.len() && x1@[i] == x2@[i] ==> result@[i] == 0,
        /* Anti-commutativity property */
        forall|i: int| 0 <= i < result.len() ==> result@[i] == -(x2@[i] - x1@[i])
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): iterative subtraction with loop invariant relating built prefix to specification */
    let mut res: Vec<i8> = Vec::new();
    let mut j: usize = 0_usize;
    while j < x1.len()
        invariant
            j <= x1.len(),
            res.len() == j,
            x1.len() == x2.len(),
            forall|i: int| 0 <= i < res.len() ==> res@[i] == x1@[i] - x2@[i],
        decreases
            x1.len() - j
    {
        let a: i8 = x1[j];
        let b: i8 = x2[j];
        let v: i8 = sub_elem(a, b);
        res.push(v);
        j = j + 1_usize;
    }
    res
}
// </vc-code>


}
fn main() {}