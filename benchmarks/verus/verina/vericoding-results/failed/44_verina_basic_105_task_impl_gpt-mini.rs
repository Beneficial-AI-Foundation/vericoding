// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): commutativity proof for multiplication */
fn mul_commutative(x: i32, y: i32)
    ensures x * y == y * x,
{
    proof {
        assert(x * y == y * x);
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
    /* code modified by LLM (iteration 5): use usize indices and prove spec with int-indexed invariants */
    let mut res: Vec<i32> = Vec::new();
    let len: usize = a.len();
    let mut i: usize = 0;
    while i < len
        invariant
            (i as int) >= 0,
            res.len() == i,
            forall|j: int| 0 <= j && j < (i as int) ==> res[(j as usize)] == a[(j as usize)] * b[(j as usize)],
        decreases (len as int) - (i as int)
    {
        let ai: i32 = a[i];
        let bi: i32 = b[i];
        let prod: i32 = ai * bi;
        res.push(prod);
        i = i + 1;
    }
    proof {
        assert(res.len() == len);
        assert(forall|k: int| 0 <= k && k < (len as int) ==> res[(k as usize)] == a[(k as usize)] * b[(k as usize)]);
    }
    res
}
// </vc-code>

}
fn main() {}