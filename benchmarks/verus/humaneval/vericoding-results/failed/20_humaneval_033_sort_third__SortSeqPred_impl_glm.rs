// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): replaced vstd::seq_lib::sort with the built-in Vec::sort method */
fn sort_vec_i8(v: &mut Vec<i8>)
    ensures
        v@.is_sorted(|a, b| a <= b),
        v@.to_multiset() == old(v)@.to_multiset(),
{
    v.sort(|a, b| a <= b);
}
// </vc-helpers>

// <vc-spec>
fn sort_seq_pred(s: Vec<i8>, p: Vec<bool>) -> (sorted: Vec<i8>)
  requires s.len() == p.len(),
  ensures 
    sorted.len() == s.len(),
    forall|i: int, j: int| 0 <= i < j < sorted.len() && p[i] && p[j] ==> sorted[i] as int <= sorted[j] as int,
    s@.to_multiset() == sorted@.to_multiset(),
    forall|i: int| 0 <= i < s.len() && !p[i] ==> sorted[i] == s[i],
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): using the helper function that now uses the built-in Vec::sort method */
{
    let mut sorted = s.clone();
    let mut true_values: Vec<i8> = Vec::new();
    for i in 0..s.len() {
        if p[i] {
            true_values.push(s[i]);
        }
    }
    sort_vec_i8(&mut true_values);
    let mut true_index = 0;
    for i in 0..sorted.len() {
        if p[i] {
            sorted[i] = true_values[true_index];
            true_index += 1;
        }
    }
    sorted
}
// </vc-code>


}

fn main() {}