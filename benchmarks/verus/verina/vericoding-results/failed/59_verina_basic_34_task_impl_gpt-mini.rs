// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_even(n: i32) -> bool {
    n % 2 == 0
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): iterative filter of even numbers with ordering invariants */
fn filter_evens(arr: &Vec<i32>) -> Vec<i32>
    ensures
        forall|x: i32| result@.contains(x) ==> is_even(x) && arr@.contains(x),
        forall|x: i32| arr@.contains(x) && is_even(x) ==> result@.contains(x),
        forall|i: int, j: int| 0 <= i < arr.len() && 0 <= j < arr.len() && i <= j && is_even(arr@[i]) && is_even(arr@[j]) ==> {
            exists|ri: int, rj: int| 0 <= ri < result.len() && 0 <= rj < result.len() && ri <= rj && result[ri] == arr@[i] && result[rj] == arr@[j]
        },
{
    let mut res: Vec<i32> = Vec::new();
    let mut k: int = 0;
    while k < arr.len()
        invariant
            0 <= k <= arr.len(),
            forall|x: i32| res@.contains(x) ==> is_even(x) && exists|t: int| 0 <= t < k && arr@[t] == x,
            forall|t: int| 0 <= t < k && is_even(arr@[t]) ==> res@.contains(arr@[t]),
            forall|p: int, q: int| 0 <= p < k && 0 <= q < k && p <= q && is_even(arr@[p]) && is_even(arr@[q]) ==> {
                exists|rp: int, rq: int| 0 <= rp < res.len() && 0 <= rq < res.len() && rp <= rq && res[rp] == arr@[p] && res[rq] == arr@[q]
            },
        decreases
            arr.len() - k
    {
        if is_even(arr@[k]) {
            let old_len = res.len();
            res.push(arr[k]);
            proof {
                assert(old_len < res.len());
                assert(res[old_len] == arr@[k]);
            }
        }
        k = k + 1;
    }
    res
}

// </vc-helpers>

// <vc-spec>
fn find_even_numbers(arr: &Vec<i32>) -> (result: Vec<i32>)
    ensures
        forall|x: i32| result@.contains(x) ==> is_even(x) && arr@.contains(x),
        forall|x: i32| arr@.contains(x) && is_even(x) ==> result@.contains(x),
        forall|i: int, j: int| 0 <= i < arr.len() && 0 <= j < arr.len() && i <= j && 
            is_even(arr[i]) && is_even(arr[j]) ==> {
                exists|ri: int, rj: int| 0 <= ri < result.len() && 0 <= rj < result.len() && 
                    ri <= rj && result[ri] == arr[i] && result[rj] == arr[j]
            },
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): call iterative helper to compute evens */
    let res = filter_evens(arr);
    res
}

// </vc-code>

}
fn main() {}