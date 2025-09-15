// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): introduce predicate for middle indices used in invariants */
spec fn is_middle_index(i: int, len: int) -> bool { 1 <= i && i < len - 1 }
// </vc-helpers>

// <vc-spec>
fn swap_first_and_last(a: &Vec<i32>) -> (result: Vec<i32>)
    requires a.len() > 0,
    ensures
        result.len() == a.len(),
        result[0] == a[a.len() - 1],
        result[result.len() - 1] == a[0],
        forall|i: int| 1 <= i < result.len() - 1 ==> result[i] == a[i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): build result via pushes and a loop invariant instead of using swap */
    let n = a.len();
    if n == 1 {
        return a.clone();
    }
    let mut res: Vec<i32> = Vec::new();
    // place last element first
    res.push(a[n - 1]);
    let mut i: usize = 1;
    while i < n - 1
        invariant
            a.len() == n,
            n >= 2,
            1 <= i && i <= n - 1,
            res.len() == i,
            res.len() >= 1,
            res@[0] == a@[(n as int) - 1],
            forall|j: int| 1 <= j && j < i as int ==> res@[j] == a@[j],
        decreases (n as int - 1 - i as int)
    {
        res.push(a[i]);
        i = i + 1;
    }
    // place first element last
    res.push(a[0]);
    res
}
// </vc-code>

}
fn main() {}