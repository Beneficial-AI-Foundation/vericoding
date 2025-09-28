// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn comparison(a: Seq<char>, b: Seq<char>, i: int) -> bool
    recommends 0 <= i <= a.len() && 0 <= i <= b.len()
    decreases a.len() - i, b.len() - i
{
    if (i < a.len() && i < b.len()) {
        if a[i] < b[i] {
            true
        } else if a[i] > b[i] {
            false
        } else {
            comparison(a, b, i + 1)
        }
    } else {
        if a.len() <= b.len() {
            true
        } else {
            false
        }
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): kept helper from previous iteration */
spec fn is_sorted_by_len(s: Seq<Vec<char>>) -> bool {
    forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i].len() <= s[j].len()
}
// </vc-helpers>

// <vc-spec>
fn sorted_list_sum(list: Vec<Vec<char>>) -> (sorted: Vec<Vec<char>>)
    requires 
        list@.len() > 0
    ensures 
        sorted@.len() <= list@.len(),
        forall|i: int| 0 <= i < sorted@.len() ==> sorted@[i].len() % 2 == 0,
        forall|x: int, y: int| 0 <= x < y < sorted@.len() ==> sorted@[x].len() <= sorted@[y].len(),
        sorted@.to_multiset().subset_of(list@.to_multiset())
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): fixed incorrect path to `lemma_swap_preserves_multiset` to fix compilation */
{
    let mut filtered_list = Vec::new();
    let mut i: usize = 0;
    while i < list.len()
        invariant
            0 <= i <= list.len(),
            forall|k: int| 0 <= k < filtered_list@.len() ==> filtered_list@[k].len() % 2 == 0,
            filtered_list@.to_multiset().subset_of(list@.to_multiset()),
    {
        let item = &list[i];
        if item.len() % 2 == 0 {
            filtered_list.push(item.clone());
        }
        i = i + 1;
    }

    let ghost filtered_list_seq = filtered_list@;
    let mut j: usize = 0;
    while j < filtered_list.len()
        invariant
            0 <= j <= filtered_list.len(),
            is_sorted_by_len(filtered_list@.subrange(0, j as int)),
            filtered_list@.to_multiset() == filtered_list_seq.to_multiset(),
            forall|k: int| 0 <= k < filtered_list@.len() ==> filtered_list@[k].len() % 2 == 0,
    {
        let mut k = j;
        while k > 0 && filtered_list[k-1].len() > filtered_list[k].len()
            invariant
                0 <= j < filtered_list.len(),
                0 < k <= j,
                filtered_list@.to_multiset() == old(filtered_list)@.to_multiset(),
                is_sorted_by_len(old(filtered_list)@.subrange(0, j as int)),
                forall|l: int| 0 <= l < filtered_list.len() ==> filtered_list@[l].len() % 2 == 0,
        {
            proof {
                vstd::seq_lib::lemma_swap_preserves_multiset(filtered_list@, (k-1) as int, k as int);
            }
            filtered_list.swap(k-1, k);
            k = k - 1;
        }
        j = j + 1;
    }
    
    return filtered_list;
}
// </vc-code>


}

fn main() {}