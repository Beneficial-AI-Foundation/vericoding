// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Lemma that Vec sequence length equals Vec length */
proof fn vec_seq_len_eq(a: &Vec<i32>)
    ensures
        (a@).len() == a.len() as int,
{
    assert((a@).len() == a.len() as int);
}

// </vc-helpers>

// <vc-spec>
fn linear_search(a: &Vec<i32>, e: i32) -> (result: usize)
    ensures
        result <= a.len(),
        result == a.len() || a[result as int] == e,
        forall|i: int| 0 <= i < result ==> a[i] != e,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): use runtime Vec indexing and spec-level sequence in invariants */
    let mut j: usize = 0;
    while j < a.len()
        invariant
            j <= a.len(),
            forall|k: int| 0 <= k < (j as int) ==> a@[k] != e,
        decreases a.len() - j
    {
        if a[j] == e {
            return j;
        }
        j += 1;
    }
    j
}

// </vc-code>

}
fn main() {}