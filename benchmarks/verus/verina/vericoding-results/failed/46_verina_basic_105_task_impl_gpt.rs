// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): simple min spec helper, not used but provided for completeness */
spec fn min(a: int, b: int) -> int { if a < b { a } else { b } }
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
    /* code modified by LLM (iteration 2): added decreases clause and refined loop invariants to ensure termination and correctness */
    let n = a.len();
    let mut res: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            a.len() == n,
            b.len() == n,
            res.len() == i,
            i <= n,
            forall|j: int| 0 <= j < i as int ==> res[j] == a[j] * b[j]
        decreases (n as int) - (i as int)
    {
        let prod = a[i] * b[i];
        res.push(prod);
        i = i + 1;
    }
    res
}
// </vc-code>

}
fn main() {}