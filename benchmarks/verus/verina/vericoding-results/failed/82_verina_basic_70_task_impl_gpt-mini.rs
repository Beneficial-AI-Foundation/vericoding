// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): vec_index_agree proves runtime and spec indexing agree */
proof fn vec_index_agree(a: &Vec<i32>, idx: int)
    requires 0 <= idx && idx < a.len() as int,
    ensures a[idx as usize] == a@[idx],
{
    proof {
        assert(idx as usize < a.len());
        assert(a[idx as usize] == a@[idx]);
    }
}

/* helper modified by LLM (iteration 5): vec_index_eq_pred lifts equality to predicates */
proof fn vec_index_eq_pred(a: &Vec<i32>, idx: int, q: spec_fn(i32) -> bool)
    requires 0 <= idx && idx < a.len() as int,
    ensures q(a[idx as usize]) == q(a@[idx]),
{
    proof {
        vec_index_agree(a, idx);
        assert(a[idx as usize] == a@[idx]);
        assert(q(a[idx as usize]) == q(a@[idx]));
    }
}
// </vc-helpers>

// <vc-spec>
fn linear_search3(a: &Vec<i32>, p: spec_fn(i32) -> bool) -> (result: usize)
    requires 
        exists|i: int| 0 <= i < a.len() && p(a[i]),
    ensures 
        result < a.len(),
        p(a[result as int]),
        forall|k: int| 0 <= k < result ==> !p(a[k]),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): use runtime indexing a[i] in condition and maintain loop invariants with spec a@ in ghost proofs */
    let mut i: usize = 0;
    while i < a.len()
        invariant
            exists|j: int| (i as int) <= j && j < a.len() as int && p(a@[j]),
            forall|k: int| 0 <= k && k < (i as int) ==> !p(a@[k]),
        decreases a.len() - i
    {
        if p(a[i]) {
            return i;
        } else {
            proof {
                let j0 = choose|j: int| (i as int) <= j && j < a.len() as int && p(a@[j]);
                assert(!p(a[i]));
                if j0 == (i as int) {
                    vec_index_eq_pred(a, i as int, p);
                    assert(p(a[i]) == p(a@[i as int]));
                    assert(p(a@[i as int]));
                    assert(false);
                } else {
                    assert((i as int) + 1 <= j0);
                    assert(j0 < a.len() as int);
                    assert(p(a@[j0]));
                    exists|j: int| (i as int) + 1 <= j && j < a.len() as int && p(a@[j]);
                }
            }
            i += 1;
        }
    }
    i
}
// </vc-code>

}
fn main() {}