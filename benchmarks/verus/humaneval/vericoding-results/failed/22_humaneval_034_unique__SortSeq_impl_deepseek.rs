// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

proof fn lemma_seq_sorted_by_insertion(s: Seq<i8>, sorted: Seq<i8>) 
    requires 
        sorted.len() == s.len(),
        s.to_multiset() == sorted.to_multiset(),
        forall|i: int, j: int| 0 <= i < j < sorted.len() ==> sorted[i] <= sorted[j]
    ensures 
        true
{
}

/* helper modified by LLM (iteration 5): fix indexing to use @ operator */
fn insert_sorted(vec: &mut Vec<i8>, index: usize, value: i8) 
    requires 
        old(vec).len() > 0,
        index < old(vec).len(),
        forall|i: int, j: int| 0 <= i < j < old(vec).len() ==> old(vec)@[i] <= old(vec)@[j]
    ensures 
        vec@.len() == old(vec)@.len() + 1,
        forall|i: int, j: int| 0 <= i < j < vec@.len() ==> vec@[i] <= vec@[j],
        vec@.to_multiset() == old(vec)@.to_multiset().insert(value)
{
    let mut i = index;
    vec.insert(index, value);
    
    while i > 0 && vec@[i] < vec@[i - 1] 
        invariant 
            i <= vec@.len(),
            vec@.len() == old(vec)@.len() + 1,
            vec@.to_multiset() == old(vec)@.to_multiset().insert(value),
            forall|k: int, l: int| 0 <= k < l < vec@.len() && (k != i || l != i - 1) ==> vec@[k] <= vec@[l]
        decreases i
    {
        vec.swap(i, i - 1);
        i -= 1;
    }
}

proof fn lemma_seq_to_multiset_eq(s1: Seq<i8>, s2: Seq<i8>)
    requires 
        s1.to_multiset() == s2.to_multiset()
    ensures 
        true
{
}

// </vc-helpers>

// <vc-spec>
fn sort_seq(s: Vec<i8>) -> (sorted: Vec<i8>)
    ensures 
        forall|i: int, j: int| 0 <= i < j < sorted@.len() ==> sorted@[i] <= sorted@[j],
        sorted@.len() == s@.len(),
        s@.to_multiset() == sorted@.to_multiset()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fix indexing to use @ operator and correct types */
    let mut sorted_vec: Vec<i8> = Vec::new();
    
    for i in 0..s.len() 
        invariant 
            sorted_vec@.len() == i as int,
            forall|k: int, l: int| 0 <= k < l < sorted_vec@.len() ==> sorted_vec@[k] <= sorted_vec@[l],
            sorted_vec@.to_multiset() == s@.subrange(0, i as int).to_multiset()
    {
        if sorted_vec.is_empty() {
            sorted_vec.push(s[i]);
        } else {
            let mut insert_index: usize = 0;
            while insert_index < sorted_vec.len() && sorted_vec@[insert_index] < s[i] as i8
                invariant 
                    insert_index <= sorted_vec@.len(),
                    forall|k: int| 0 <= k < insert_index ==> sorted_vec@[k] <= s[i] as i8
                decreases sorted_vec.len() - insert_index
            {
                insert_index += 1;
            }
            insert_sorted(&mut sorted_vec, insert_index, s[i] as i8);
        }
    }
    
    lemma_seq_sorted_by_insertion(s@, sorted_vec@);
    sorted_vec
}
// </vc-code>


}

fn main() {}