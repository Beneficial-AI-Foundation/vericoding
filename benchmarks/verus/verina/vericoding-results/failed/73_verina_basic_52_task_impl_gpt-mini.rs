// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): recursive argmin helper without requires/ensures */
spec fn argmin_from(s: Seq<i32>, i: int) -> int {
    if i + 1 == s.len() {
        i
    } else {
        let k = argmin_from(s, i + 1);
        if s[i] <= s[k] { i } else { k }
    }
}
// </vc-helpers>

// <vc-spec>
fn bubble_sort(a: &Vec<i32>) -> (result: Vec<i32>)
    ensures
        result.len() == a.len(),
        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] <= result[j],
        a@.to_multiset() == result@.to_multiset(),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): selection-based extraction producing sorted result */
    let mut pool = a.clone();
    let mut res: Vec<i32> = Vec::new();
    let n = pool.len();

    let mut i = 0usize;
    while i < n {
        // find index of minimum in pool
        let mut mi: usize = 0;
        let mut j: usize = 1;
        while j < pool.len() {
            if pool[j] < pool[mi] {
                mi = j;
            }
            j += 1;
        }

        let v = pool.remove(mi);
        res.push(v);
        i += 1;
    }

    res
}
// </vc-code>

}
fn main() {}