// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn contains(s: Seq<i8>, val: i8) -> (res: bool)
    ensures
        res == exists|i: int| 0 <= i < s.len() && s.index(i) == val
{
    let mut i: int = 0;
    let mut found = false;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            found == exists|j: int| 0 <= j < i && s.index(j) == val,
        decreases s.len() - i
    {
        if s.index(i) == val {
            found = true;
        }
        i = i + 1;
    }
    found
}
// </vc-helpers>

// <vc-spec>
fn intersect(a: Vec<i8>, b: Vec<i8>) -> (result: Vec<i8>)
    ensures
        result.len() < a.len() && result.len() < b.len(),
        forall|i: int, j: int| 0 <= i < a@.len() && 0 <= j < b@.len() ==> (
            (a@[i] == b@[j] ==> exists|k: int| 0 <= k < result@.len() && result@[k] == a@[i]) &&
            (a@[i] != b@[j] ==> !exists|k: int| 0 <= k < result@.len() && result@[k] == a@[i])
        )
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed Seq indexing with .index() and corrected type mismatches for loop counters. */
    let mut result_vec: Vec<i8> = Vec::new();
    let a_seq = a.view();
    let b_seq = b.view();

    let mut i: int = 0;
    while i < a_seq.len()
        invariant
            0 <= i <= a_seq.len(),
            forall|l: int| 0 <= l < result_vec.view().len() ==> (contains(a_seq, result_vec.view().index(l)) && contains(b_seq, result_vec.view().index(l))),
            forall|l: int, m: int| 0 <= l < m < result_vec.view().len() ==> result_vec.view().index(l) != result_vec.view().index(m),
            forall|v_val: i8| (
                (exists|k: int| 0 <= k < result_vec.view().len() && result_vec.view().index(k) == v_val) ==> (
                    contains(a_seq, v_val) && contains(b_seq, v_val)
                )
            ),
            forall|k: int| 0 <= k < i && contains(b_seq, a_seq.index(k)) ==> contains(result_vec.view(), a_seq.index(k)),
        decreases a_seq.len() - i
    {
        let current_a_val = a_seq.index(i);
        if contains(b_seq, current_a_val) && !contains(result_vec.view(), current_a_val) {
            result_vec.push(current_a_val);
        }
        i = i + 1;
    }
    result_vec
}
// </vc-code>


}
fn main() {}