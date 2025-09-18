// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): lemma showing fold_left selects the element at the given valid index */
proof fn lemma_fold_left_returns_at_index(arr: Seq<f64>, i: nat)
    requires i < arr.len()
    ensures fold_left(arr, i) == arr[i as int]
{
    if i == 0 {
        assert(fold_left(arr, i) == arr[0 as int]);
        assert(arr[0 as int] == arr[i as int]);
    } else {
        assert(i > 0);
        assert(fold_left(arr, i) == arr[i as int]);
    }
}

/* helper modified by LLM (iteration 5): spec for computing the last valid index (returns 0 on empty) */
spec fn last_index(len: nat) -> nat
{
    if len == 0 { 0 } else { (len - 1) as nat }
}
// </vc-helpers>

// <vc-spec>
spec fn fold_left(arr: Seq<f64>, index: nat) -> f64
    decreases index
{
    if index == 0 {
        arr[0 as int]
    } else {

        arr[index as int]
    }
}

fn reduce(arr: Vec<f64>) -> (result: f64)
    requires arr.len() > 0,
    ensures 
        arr.len() == 1 ==> result == arr[0],
        arr.len() > 1 ==> result == fold_left(arr@, (arr.len() - 1) as nat)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): compute and return the last element; prove it matches fold_left at last index */
    let n = arr.len();
    if n > 1 {
        let idx = n - 1;
        let r = arr[idx];
        proof {
            assert(arr@.len() == n as nat);
            assert((idx as nat) < arr@.len());
            lemma_fold_left_returns_at_index(arr@, idx as nat);
            assert(fold_left(arr@, idx as nat) == arr@[(idx as int)]);
            assert(r == arr@[(idx as int)]);
        }
        r
    } else {
        arr[0]
    }
}
// </vc-code>

}
fn main() {}