// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): sequence concatenation helper */
spec fn seq_concat(a: Seq<i32>, b: Seq<i32>) -> Seq<i32> { a + b }
// </vc-helpers>

// <vc-spec>
fn selection_sort(a: &Vec<i32>) -> (result: Vec<i32>)
    ensures
        result.len() == a.len(),
        forall|i: int, j: int| 0 <= i <= j < result.len() ==> result[i] <= result[j],
        result@ =~= a@,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): selection sort with inner invariant for min index and proof of invariant preservation */
    let mut v = a.clone();
    let mut res: Vec<i32> = Vec::new();

    while v.len() > 0
        invariant
            forall|p: int, q: int| 0 <= p && p <= q && q < (res.len() as int) ==> res@[p] <= res@[q],
            forall|p: int, q: int| 0 <= p < (res.len() as int) && 0 <= q < (v.len() as int) ==> res@[p] <= v@[q],
            seq_concat(res@, v@) =~= a@,
        decreases v.len() as int
    {
        let mut min_idx: usize = 0;
        let mut k: usize = 1;
        while k < v.len()
            invariant
                0 <= (k as int) && (k as int) <= (v.len() as int),
                0 <= (min_idx as int) && (min_idx as int) < (v.len() as int),
                forall|q: int| 0 <= q && q < (k as int) ==> v@[min_idx] <= v@[q],
            decreases (v.len() as int) - (k as int)
        {
            if v[k] < v[min_idx] {
                min_idx = k;
            }
            k += 1;
        }
        let old_res_len = res.len();
        let x = v.remove(min_idx);
        res.push(x);
        proof {
            // Use the inner-loop fact that v@[min_idx] is minimal among the old v elements
            // and the outer-loop fact that all old res elements are <= all old v elements
            // to establish the required invariants after removing and pushing the minimum.
            assert(old_res_len as int >= 0);
            assert(forall|p: int| 0 <= p && p < (old_res_len as int) ==> res@[p] <= res@[(old_res_len as int)]);
            assert(forall|p: int, q: int| 0 <= p && p < (res.len() as int) && 0 <= q && q < (v.len() as int) ==> res@[p] <= v@[q]);
            assert(seq_concat(res@, v@) =~= a@);
        }
    }

    res
}
// </vc-code>

}
fn main() {}