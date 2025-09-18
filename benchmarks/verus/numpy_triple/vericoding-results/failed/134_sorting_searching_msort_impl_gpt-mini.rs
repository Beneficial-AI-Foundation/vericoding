// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): basic integer min */
fn min(a: int, b: int) -> int { if a < b { a } else { b } }
// </vc-helpers>

// <vc-spec>
fn msort(a: Vec<i32>) -> (result: Vec<i32>)
    ensures
        result.len() == a.len(),
        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] <= result[j],
        result@.to_multiset() =~= a@.to_multiset(),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): selection sort with correct '@' indexing and invariants */
    let mut v = a.clone();
    let mut res: Vec<i32> = Vec::new();
    while v.len() > 0
        invariant res.len() + v.len() == a.len(),
        invariant forall|i: int, j: int| 0 <= i && i < j && j < res.len() as int ==> res@[i] <= res@[j],
        invariant forall|ri: int, vi: int| 0 <= ri && ri < res.len() as int && 0 <= vi && vi < v.len() as int ==> res@[ri] <= v@[vi],
        invariant res@.to_multiset() + v@.to_multiset() =~= a@.to_multiset(),
        decreases v.len()
    {
        let mut min_idx: int = 0;
        let mut i: int = 1;
        while i < v.len() as int
            invariant 0 <= min_idx && min_idx < v.len() as int,
            invariant 0 <= i && i <= v.len() as int,
            invariant forall|k: int| 0 <= k && k < i ==> v@[min_idx] <= v@[k],
            decreases (v.len() as int - i)
        {
            if v@[i] < v@[min_idx] {
                min_idx = i;
            }
            i = i + 1;
        }
        let x = v.remove(min_idx as usize);
        res.push(x);
        proof {
            assert(res@.to_multiset() + v@.to_multiset() =~= a@.to_multiset());
            assert(forall|ri: int, vi: int| 0 <= ri && ri < res.len() as int && 0 <= vi && vi < v.len() as int ==> res@[ri] <= v@[vi]);
            assert(forall|p: int, q: int| 0 <= p && p < q && q < res.len() as int ==> res@[p] <= res@[q]);
        }
    }
    res
}
// </vc-code>

}
fn main() {}