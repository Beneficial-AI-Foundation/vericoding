// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed compilation errors by changing nat to usize, nat!(0) to 0, add(nat!(1)) to +1, and [i as int] to [i as usize] for Seq indexing */
spec fn is_sorted(seq: Seq<i8>) -> bool {
    forall |i: int, j: int| 0 <= i < j < seq.len() ==> (seq[i] as int <= seq[j] as int)
}

spec fn sorted_insert(elem: i8, seq: Seq<i8>) -> (result: Seq<i8>)
    requires
        is_sorted(seq),
    ensures
        is_sorted(result),
        result.len() == seq.len() + 1,
        result.to_multiset() == seq.to_multiset().insert(elem),
{
    let mut result = Seq::empty();
    let mut i: usize = 0;
    let mut inserted = false;
    while i < seq.len() || !inserted
        invariant
            i <= seq.len(),
            is_sorted(result),
            result.len() == i + (if inserted { 1 } else { 0 }),
        decreases seq.len() - i + (if inserted { 0 } else { 1 })
    {
        if !inserted && (i == seq.len() || seq[i as usize] > elem) {
            result = result.push(elem);
            inserted = true;
        }
        if i < seq.len() {
            result = result.push(seq[i as usize]);
            i = i + 1;
        }
    }
    result
}

spec fn sort(seq: Seq<i8>) -> (result: Seq<i8>)
    requires
        true,
    ensures
        is_sorted(result),
        result.to_multiset() == seq.to_multiset(),
        result.len() == seq.len(),
{
    let mut result = Seq::empty();
    let mut i: usize = 0;
    while i < seq.len()
        invariant
            i <= seq.len(),
            is_sorted(result),
            result.len() == i,
            result.to_multiset() + seq.slice(i, seq.len()).to_multiset() == seq.to_multiset(),
        decreases seq.len() - i
    {
        result = sorted_insert(seq[i as usize], result);
        i = i + 1;
    }
    result
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
{
    /* code modified by LLM (iteration 5): Fixed compilation errors by changing nat to usize, nat!(0) to 0, add(nat!(1)) to +1, and kept [i as int] for Seq/View indexing */
    let mut sorted_to_sort: Seq<i8> = Seq::empty();
    let mut index: usize = 0;
    let mut true_count: usize = 0;
    while index < (s@.len() as usize)
        invariant
            index <= (s@.len() as usize),
            sorted_to_sort.len() == true_count,
        decreases (s@.len() as usize) - index
    {
        if s@[index as int] {
            sorted_to_sort = sorted_to_sort.push(s@[index as int]);
            true_count = true_count + 1;
        }
        index = index + 1;
    }
    let sorted_extract = sort(sorted_to_sort);
    let mut result_vec = Vec::new();
    let mut i: usize = 0;
    let mut sorted_idx: usize = 0;
    while i < (p@.len() as usize)
        invariant
            i <= (p@.len() as usize),
            sorted_idx <= true_count,
        decreases (p@.len() as usize) - i
    {
        if p@[i as int] {
            result_vec.push(sorted_extract.view()[sorted_idx as int]);
            sorted_idx = sorted_idx + 1;
        } else {
            result_vec.push(s@[i as int]);
        }
        i = i + 1;
    }
    result_vec
}
// </vc-code>


}

fn main() {}