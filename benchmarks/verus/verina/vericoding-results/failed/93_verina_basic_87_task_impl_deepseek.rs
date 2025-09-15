// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn find_min_index(s: Seq<i32>, start: int) -> (idx: int)
    requires 0 <= start <= s.len()
    ensures start <= idx <= s.len(),
            forall|i: int| start <= i < s.len() ==> s[idx] <= s[i]
{
    if start >= s.len() {
        start
    } else {
        let min_rest = find_min_index(s, start + 1);
        if s[start] <= s[min_rest] {
            start
        } else {
            min_rest
        }
    }
}

proof fn lemma_find_min_index_valid(s: Seq<i32>, start: int)
    requires 0 <= start <= s.len()
    ensures start <= find_min_index(s, start) <= s.len()
{
    if start < s.len() {
        lemma_find_min_index_valid(s, start + 1);
    }
}
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
    /* code modified by LLM (iteration 2): Fixed type conversion and variable resolution */
    let mut result = a.clone();
    let mut i: usize = 0;
    while i < result.len()
        invariant
            0 <= i <= result.len(),
            forall|k: int, l: int| 0 <= k <= l < i ==> result@[k] <= result@[l],
            result@ =~= a@,
            i >= 0
    {
        let s_seq = result@;
        let min_idx_val = find_min_index(s_seq, i as int);
        proof {
            lemma_find_min_index_valid(s_seq, i as int);
        }
        let min_idx: usize = min_idx_val as usize;
        if min_idx != i {
            let temp = result[i];
            result[i] = result[min_idx];
            result[min_idx] = temp;
            proof {
                lemma_swap_maintains_permutation(s_seq, i as int, min_idx as int);
            }
        }
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}