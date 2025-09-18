// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fix type handling and add proper lemmas */
fn div_lemma_usize(x: usize, y: usize)
    requires y > 0
    ensures x / y >= 0 && x / y <= x
{
}

proof fn index_bound_lemma(idx: usize, repeats: usize, len: usize)
    requires
        repeats > 0,
        idx < len * repeats
    ensures
        (idx / repeats) < len
{
}

spec fn valid_index(idx: usize, repeats: usize, len: usize) -> bool
    requires repeats > 0
    ensures (idx / repeats) < len == valid_index(idx, repeats, len)
{
    idx < len * repeats
}
// </vc-helpers>

// <vc-spec>
fn repeat<T: Copy>(a: Vec<T>, repeats: usize) -> (result: Vec<T>)
    requires repeats > 0,
    ensures
        result.len() == a.len() * repeats,
        forall|i: int| #![trigger result[i]] 0 <= i < result.len() ==> {
            let k = i / (repeats as int);
            0 <= k < a.len() && result[i] == a[k]
        },
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fix type conversion and ensure proper indexing */
{
    let len = a.len();
    let total_len = len * repeats;
    let mut result: Vec<T> = Vec::new();
    let mut idx: usize = 0;

    while idx < total_len
        invariant
            idx <= total_len,
            result.len() == idx,
            forall|i: int| #![trigger result@[i]] 0 <= i < idx ==> {
                let k = (i as usize) / repeats;
                k < len && result@[i] == a@[k as int]
            },
        decreases total_len - idx
    {
        let k: usize = idx / repeats;
        proof { index_bound_lemma(idx, repeats, len); }
        result.push(a[k]);
        idx = idx + 1;
    }
    result
}
// </vc-code>

}
fn main() {}