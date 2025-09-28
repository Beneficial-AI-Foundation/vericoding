// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): prove sequence length equals vector length */
fn lemma_seq_len_eq_vec_len<T>(v: Vec<T>)
    ensures
        v.len() == (v@.len() as nat),
{
    proof {
        assert(v.len() == (v@.len() as nat));
    }
}
// </vc-helpers>

// <vc-spec>
fn in1d<T: PartialEq>(ar1: Vec<T>, ar2: Vec<T>) -> (result: Vec<bool>)
    ensures 
        result.len() == ar1.len(),
        forall|i: int| 0 <= i < ar1@.len() ==> 
            result@[i] == exists|j: int| 0 <= j < ar2@.len() && ar1@[i] == ar2@[j]
// </vc-spec>
// <vc-code>
{
/* code modified by LLM (iteration 5): add bounds invariants for safe indexing and maintain result mapping */
    let mut result: Vec<bool> = Vec::new();
    let mut i: usize = 0;
    while i < ar1.len()
        invariant
            result.len() == i,
            0 <= (i as int) <= ar1@.len(),
            forall|k: int| 0 <= k < (i as int) ==> result@[k] == exists|j: int| 0 <= j < ar2@.len() && ar1@[k] == ar2@[j],
        decreases ar1.len() - i
    {
        let mut j: usize = 0;
        let mut found: bool = false;
        while j < ar2.len()
            invariant
                0 <= (i as int) < ar1@.len(),
                0 <= (j as int) <= ar2@.len(),
                found == exists|k: int| 0 <= k < (j as int) && ar1@[(i as int)] == ar2@[k],
            decreases ar2.len() - j
        {
            if ar1[i] == ar2[j] {
                found = true;
                j = ar2.len();
            } else {
                j = j + 1;
            }
        }
        result.push(found);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}