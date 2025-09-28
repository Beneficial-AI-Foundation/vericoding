// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn extract(condition: &Vec<bool>, arr: &Vec<i8>) -> (result: Vec<i8>)
    requires condition.len() == arr.len(),
    ensures
        /* Each element in result comes from arr at a position where condition is true */
        forall|k: int| 0 <= k < result@.len() ==>
            exists|i: int| 0 <= i < arr@.len() && condition@[i] == true && #[trigger] result@[k] == arr@[i],
        /* Every True position in condition contributes exactly one element to the result */
        forall|i: int| 0 <= i < condition@.len() && condition@[i] == true ==>
            exists|k: int| 0 <= k < result@.len() && #[trigger] result@[k] == arr@[i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Changed to use int for loop index and added bounds check */
    let n = condition.len();
    let mut res = Vec::new();
    let mut i: int = 0;
    while i < n as int
        invariant
            0 <= i <= n as int,
            condition.len() == n,
            arr.len() == n,
            forall|k: int| 0 <= k < res@.len() ==> exists|j: int| 0 <= j < i && condition@[j] == true && #[trigger] res@[k] == arr@[j],
            forall|j: int| 0 <= j < i && condition@[j] == true ==> exists|k: int| 0 <= k < res@.len() && #[trigger] res@[k] == arr@[j],
        decreases (n as int - i) as nat
    {
        let i_usize = i as usize;
        assert(i_usize < n); // from i < n as int and n as int is non-negative because n is usize
        if condition[i_usize] {
            res.push(arr[i_usize]);
        }
        i += 1;
    }
    res
}
// </vc-code>


}
fn main() {}