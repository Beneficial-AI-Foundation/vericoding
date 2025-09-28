// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): create a 2-element vector pair */
fn make_pair(a: i8, b: i8) -> (result: Vec<i8>)
    ensures
        result.len() == 2,
        result@[0] == a,
        result@[1] == b,
{
    let mut v: Vec<i8> = Vec::new();
    v.push(a);
    v.push(b);
    v
}
// </vc-helpers>

// <vc-spec>
fn c_(arr1: Vec<i8>, arr2: Vec<i8>) -> (result: Vec<Vec<i8>>)
    requires arr1.len() == arr2.len(),
    ensures 
        result.len() == arr1.len(),
        forall|i: int| 0 <= i < result.len() ==> 
            result[i]@.len() == 2 &&
            result[i][0] == arr1[i] &&
            result[i][1] == arr2[i]
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): zip two vectors into vector of pairs using sequence-based specs in invariants */
    let n: usize = arr1.len();
    let mut res: Vec<Vec<i8>> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            res.len() == i,
            forall|k: int| 0 <= k && k < (i as int) ==> res[k]@.len() == 2 && res[k]@[0] == arr1@[k] && res[k]@[1] == arr2@[k],
        decreases n - i
    {
        let a = arr1[i];
        let b = arr2[i];
        let pair = make_pair(a, b);
        res.push(pair);
        i = i + 1;
    }
    res
}
// </vc-code>

}
fn main() {}