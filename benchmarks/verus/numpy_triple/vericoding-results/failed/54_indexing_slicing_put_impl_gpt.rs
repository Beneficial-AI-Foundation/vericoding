// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): simple min function retained for general reasoning */
fn min(a: int, b: int) -> int { if a < b { a } else { b } }
/* helper modified by LLM (iteration 5): predicate for index validity */
spec fn is_valid_index(len: nat, i: nat) -> bool { i < len }
/* helper modified by LLM (iteration 5): arithmetic identity lemma */
proof fn helper_lemma_add_zero(x: int) ensures x + 0 == x { assert(x + 0 == x); }
/* helper modified by LLM (iteration 5): lemma converting usize bound to int bound */
proof fn usize_lt_to_int_lt(u: usize, n: usize)
    requires u < n
    ensures 0 <= u as int && (u as int) < n
{ 
    assert(0 <= u as int);
    assert((u as int) < n);
}
/* helper modified by LLM (iteration 5): lemma to instantiate bound from quantified precondition */
proof fn index_in_ind_bounds_implies_accessible(ind: Vec<usize>, a_len: usize, i: usize)
    requires
        forall|k: int| 0 <= k < ind.len() ==> ind[k] < a_len,
        i < ind.len()
    ensures
        ind[i as int] < a_len
{
    assert(0 <= i as int);
    assert((i as int) < ind.len());
    assert(ind[i as int] < a_len);
}
// </vc-helpers>

// <vc-spec>
fn put(a: Vec<f64>, ind: Vec<usize>, v: Vec<f64>) -> (result: Vec<f64>)
    requires 
        ind.len() == v.len(),
        forall|i: int| 0 <= i < ind.len() ==> ind[i] < a.len(),
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < ind.len() ==> result[ind[i] as int] == v[i],
        forall|j: int| 0 <= j < result.len() ==> 
            (forall|i: int| 0 <= i < ind.len() ==> j != ind[i]) ==> result[j] == a[j],
        ind.len() == 0 ==> result@ == a@,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): capture a's view as ghost and implement forward update with invariants */
    let a_len = a.len();
    let ghost a_seq = a@;
    let n = ind.len();
    let mut res = a;
    let mut i: usize = 0;
    while i < n
        invariant
            res.len() == a_len,
            n == ind.len(),
            n == v.len(),
            i <= n,
            forall|k: int| 0 <= k < i as int ==> ind[k] < a_len,
            forall|j: int| 0 <= j < res.len() ==> (forall|k: int| 0 <= k < i as int ==> j != ind[k]) ==> res[j] == a_seq[j]
        decreases n - i
    {
        let idx = ind[i];
        proof {
            index_in_ind_bounds_implies_accessible(ind, a_len, i);
            assert(ind[i as int] < res.len());
        }
        let val = v[i];
        res.set(idx, val);
        i = i + 1;
    }
    res
}
// </vc-code>

}
fn main() {}