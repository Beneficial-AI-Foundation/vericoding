// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): predicates for sortedness and bounds of index sequences */
spec fn is_sorted_stable_by(a: Seq<i32>, idxs: Seq<usize>) -> bool {
    forall|i: int, j: int|
        0 <= i < j < idxs.len() ==>
            a[idxs[i] as int] <= a[idxs[j] as int]
            && (a[idxs[i] as int] == a[idxs[j] as int] ==> idxs[i] < idxs[j])
}

/* helper modified by LLM (iteration 4): bounds predicate for indices within array length */
spec fn indices_in_bounds(n: usize, idxs: Seq<usize>) -> bool {
    forall|i: int| 0 <= i < idxs.len() ==> idxs[i] < n
}
// </vc-helpers>

// <vc-spec>
fn argsort(a: Vec<i32>) -> (result: Vec<usize>)
    ensures 
        result.len() == a.len(),

        forall|i: int| 0 <= i < result.len() ==> #[trigger] result[i] < a.len(),

        forall|i: int, j: int| 0 <= i < j < result.len() ==> 
            a[#[trigger] result[i] as int] <= a[#[trigger] result[j] as int],

        forall|i: int, j: int| 0 <= i < j < result.len() && 
            a[#[trigger] result[i] as int] == a[#[trigger] result[j] as int] ==> 
            result[i] < result[j]
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): added decreases clauses for loops to satisfy termination checking; stable insertion-based argsort */
    let n = a.len();
    let mut res: Vec<usize> = Vec::new();
    let mut k: usize = 0;
    while k < n
        decreases (n - k) as int
    {
        let mut new_res: Vec<usize> = Vec::new();
        let mut inserted: bool = false;
        let mut i: usize = 0;
        let res_len = res.len();
        while i < res_len
            decreases (res_len - i) as int
        {
            let idx = res[i];
            if !inserted {
                let ai = a[idx];
                let ak = a[k];
                if ai > ak || (ai == ak && k < idx) {
                    new_res.push(k);
                    inserted = true;
                }
            }
            new_res.push(idx);
            i += 1;
        }
        if !inserted {
            new_res.push(k);
        }
        res = new_res;
        k += 1;
    }
    res
}
// </vc-code>

}
fn main() {}