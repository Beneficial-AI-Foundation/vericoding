// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed lemma syntax by adding fn keyword */
fn lemma_mod_bounds(i: int, len: int)
    requires len > 0, i >= 0
    ensures 0 <= i % len < len
{
}

/* helper modified by LLM (iteration 5): Added lemma to help prove result indexing */
fn lemma_result_indexing(rep: int, idx: int, a_len: int, i: int)
    requires a_len > 0, rep >= 0, 0 <= idx <= a_len, i == rep * a_len + idx - 1
    ensures i % a_len == (idx - 1) % a_len
{
}
// </vc-helpers>

// <vc-spec>
fn tile(a: Vec<i32>, reps: usize) -> (result: Vec<i32>)
    requires 
        reps > 0,
        a.len() > 0,
    ensures
        result.len() == a.len() * reps,
        forall|i: int| 0 <= i < result.len() ==> result[i] == a[i % (a.len() as int)],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed type mismatch by casting idx to int when indexing result */
    let mut result: Vec<i32> = Vec::new();
    let mut rep = 0;
    while rep < reps
        invariant
            rep <= reps,
            result.len() == a.len() * rep,
            forall|i: int| 0 <= i < result.len() ==> result[i] == a[i % (a.len() as int)],
        decreases reps - rep
    {
        let mut idx = 0;
        while idx < a.len()
            invariant
                rep < reps,
                idx <= a.len(),
                result.len() == a.len() * rep + idx,
                forall|i: int| 0 <= i < a.len() * rep ==> result[i] == a[i % (a.len() as int)],
                forall|j: int| 0 <= j < idx ==> result[a.len() * rep + j] == a[j as int],
            decreases a.len() - idx
        {
            proof {
                lemma_mod_bounds(idx as int, a.len() as int);
            }
            result.push(a[idx]);
            proof {
                assert(result.len() == a.len() * rep + idx + 1);
                let new_idx = (a.len() * rep + idx) as int;
                assert(result[new_idx] == a[idx as int]);
                assert(new_idx % (a.len() as int) == idx as int);
            }
            idx += 1;
        }
        proof {
            assert(idx == a.len());
            assert(result.len() == a.len() * rep + a.len());
            assert(result.len() == a.len() * (rep + 1));
        }
        rep += 1;
    }
    result
}
// </vc-code>

}
fn main() {}