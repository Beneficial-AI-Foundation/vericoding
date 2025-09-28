// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Replace with proper lemma for sequence split multiset equivalence */
pub open spec fn elem_at_index_to_end_is_subset_multiset(s: Seq<i8>, idx: int) -> bool {
    s.to_multiset() =~= s.drop(idx).to_multiset().add_all(s.take(idx).to_multiset())
}

proof fn lemma_elem_at_index_to_end_is_subset_multiset(s: Seq<i8>, idx: int)
    requires
        0 <= idx <= s.len(),
    ensures
        s.to_multiset() =~= s.drop(idx).to_multiset().add_all(s.take(idx).to_multiset()),
{
    vstd::seq::lemma_seq_to_multiset_split_at_index(s, idx);
}

proof fn lemma_vec_insert_preserves_multiset(v: Vec<i8>, index: int, value: i8)
    requires
        0 <= index <= v@.len(),
    ensures
        v.insert(index, value)@.to_multiset() =~= v@.to_multiset().insert(value),
{
    vstd::vector::lemma_vec_insert_and_split(v, index, value);
}

spec fn get_indices_by_modulo(s: Seq<i8>, modulo_base: int, remainder: int) -> Seq<i8> {
    s.filter(|i: int| i % modulo_base == remainder)
}

spec fn is_sorted_non_empty(s: Seq<i8>) -> bool {
    forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] <= s[j]
}
// </vc-helpers>

// <vc-spec>
fn sort_third(a: &Vec<i8>) -> (sorted_even: Vec<i8>)
    requires a@.len() > 0
    ensures 
        sorted_even@.len() == a@.len(),
        forall|i: int, j: int| 0 <= i < j < sorted_even@.len() && i % 3 == 0 && j % 3 == 0 ==>
            sorted_even@[i] <= sorted_even@[j],
        forall|i: int| 0 <= i < a@.len() && i % 3 != 0 ==> sorted_even@[i] == a@[i],
        a@.to_multiset() == sorted_even@.to_multiset()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed lemma call with correct vstd function names */
{
    let mut sorted_even = a.clone();
    let len = a.len();
    let mut third_indices: Vec<usize> = Vec::new();
    let mut third_values: Vec<i8> = Vec::new();
    
    let mut i: usize = 0;
    while i < len
        invariant
            i <= len,
            0 <= i,
            third_indices@.len() == third_values@.len(),
            forall|k: int| 0 <= k < third_indices@.len() ==> third_indices@[k] % 3 == 0 && third_indices@[k] < len,
            forall|k: int| 0 <= k < third_indices@.len() ==> third_values@[k] == a@[third_indices@[k] as int],
    {
        if i % 3 == 0 {
            third_indices.push(i);
            third_values.push(a[i]);
        }
        i += 1;
    }
    
    third_values.sort();
    
    let mut j: usize = 0;
    while j < third_indices.len()
        invariant
            j <= third_indices@.len(),
            0 <= j,
            sorted_even@.len() == a@.len(),
            a@.to_multiset() == sorted_even@.to_multiset(),
            forall|k: int| 0 <= k < a@.len() && k % 3 != 0 ==> sorted_even@[k] == a@[k],
            forall|idx_idx: int| 0 <= idx_idx < j ==> sorted_even@[third_indices@[idx_idx] as int] == third_values@[idx_idx],
    {
        let idx = third_indices[j];
        sorted_even.set(idx, third_values[j]);
        j += 1;
    }
    
    sorted_even
}
// </vc-code>


}

fn main() {}