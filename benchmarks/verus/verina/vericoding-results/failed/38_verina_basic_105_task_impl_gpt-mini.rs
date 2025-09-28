// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): lemma connecting int bounds to usize bound */
proof fn int_to_usize_lt(i: int, n: usize)
    requires 0 <= i, i < n as int,
    ensures (i as usize) < n
{
    proof {
        assert((i as usize) < n);
    }
}
// </vc-helpers>

// <vc-spec>
fn array_product(a: &Vec<i32>, b: &Vec<i32>) -> (result: Vec<i32>)
    requires a.len() == b.len(),
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> result[i] == a[i] * b[i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): implement array product using int loop and maintain invariants */
    let mut res: Vec<i32> = Vec::new();
    let mut i: int = 0;
    while i < a.len() as int
        invariant
            0 <= i,
            res.len() == i as usize,
            forall|j: int| 0 <= j < i ==> res@[j] == a@[j] * b@[j],
        decreases a.len() as int - i
    {
        proof {
            // establish that i as usize is a valid index into a and b
            int_to_usize_lt(i, a.len());
        }
        let idx: usize = i as usize;
        res.push(a[idx] * b[idx]);
        i = i + 1;
    }
    res
}
// </vc-code>

}
fn main() {}