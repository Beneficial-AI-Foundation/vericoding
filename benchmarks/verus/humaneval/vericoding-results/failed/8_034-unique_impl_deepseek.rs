// <vc-preamble>
use vstd::calc;
use vstd::prelude::*;
use vstd::seq_lib::lemma_multiset_commutative;
use vstd::seq_lib::lemma_seq_contains_after_push;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Add multiset_of function definition and fix bubble sort verification */
spec fn multiset_of(s: Seq<i32>) -> Multiset<i32> {
    Multiset::from_seq(s)
}

spec fn is_sorted_strict(s: Seq<i32>) -> bool {
    forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] < s[j]
}

proof fn lemma_bubble_sort_sorted(v: Vec<i32>) -> (result: Vec<i32>)
    ensures
        is_sorted_strict(result@),
        multiset_of(result@) == multiset_of(v@),
{
    let mut sorted = v.clone();
    let len = sorted.len();
    let mut i = 0;
    
    while i < len
        invariant
            0 <= i <= len,
            is_sorted_strict(sorted@.subrange(0, len - i)),
            forall|k: int| len - i <= k < len ==> sorted@[k] >= sorted@[len - i - 1],
            multiset_of(sorted@) == multiset_of(v@),
    {
        let mut j = 0;
        while j < len - i - 1
            invariant
                0 <= j <= len - i - 1,
                is_sorted_strict(sorted@.subrange(0, j)),
                forall|k: int| j <= k < len - i - 1 ==> sorted@[k] <= sorted@[k + 1],
                multiset_of(sorted@) == multiset_of(v@),
        {
            if sorted@[j] > sorted@[j + 1] {
                sorted.swap(j, j + 1);
            }
            j += 1;
        }
        i += 1;
    }
    sorted
}
// </vc-helpers>

// <vc-spec>
fn unique(s: Vec<i32>) -> (result: Vec<i32>)

    ensures
        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] < result[j],
        forall|i: int| #![auto] 0 <= i < result.len() ==> s@.contains(result[i]),
        forall|i: int| #![trigger s[i]] 0 <= i < s.len() ==> result@.contains(s[i]),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Use lemma function to get sorted vector and implement unique filtering */
{
    let sorted = lemma_bubble_sort_sorted(s.clone());
    
    let mut result: Vec<i32> = Vec::new();
    let mut prev: Option<i32> = None;
    
    for x in sorted.iter() {
        if prev.is_none() || Some(*x) != prev {
            result.push(*x);
            prev = Some(*x);
        }
    }
    
    result
}
// </vc-code>

}
fn main() {}