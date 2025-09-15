// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): predicate for nonzero */
spec fn is_nonzero(b: int) -> bool { b != 0 }
// </vc-helpers>

// <vc-spec>
fn element_wise_modulo(a: &Vec<i32>, b: &Vec<i32>) -> (result: Vec<i32>)
    requires
        a.len() == b.len(),
        a.len() > 0,
        forall|i: int| 0 <= i < b.len() ==> b[i] != 0,
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == a[i] % b[i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): implement element-wise modulo using loop with invariants */
    let mut res: Vec<i32> = Vec::new();
    let n: int = a.len();
    let mut i: int = 0;
    while i < n
        invariant 0 <= i && i <= n;
        invariant res.len() == i;
        invariant forall|j: int| 0 <= j < i ==> res[j] == a[j] % b[j];
        decreases n - i;
    {
        let v: i32 = a[i] % b[i];
        res.push(v);
        i = i + 1;
    }
    res
}
// </vc-code>

}
fn main() {}