// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): spec helper for element-wise product at index */
spec fn vec_index_mul(a: &Vec<i32>, b: &Vec<i32>, i: int) -> i32 { a@[i] * b@[i] }
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
    /* code modified by LLM (iteration 5): implement element-wise product using precomputed int length and verified loop */
    let mut res = Vec::<i32>::new();
    let n: int = a.len() as int;
    let mut i: int = 0;
    while i < n
        invariant 0 <= i && i <= n;
        invariant (res.len() as int) == i;
        invariant forall |j: int| 0 <= j && j < i ==> res@[j] == a@[j] * b@[j];
        decreases n - i
    {
        let idx: usize = i as usize;
        let ai: i32 = a[idx];
        let bi: i32 = b[idx];
        res.push(ai * bi);
        i = i + 1;
    }
    res
}
// </vc-code>

}
fn main() {}