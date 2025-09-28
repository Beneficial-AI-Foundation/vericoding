// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_positive(x: int) -> bool {
    x > 0
}

spec fn all_positive(s: Seq<int>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> is_positive(#[trigger] s[i])
}

spec fn all_elements_from_original(result: Seq<int>, original: Seq<int>) -> bool {
    forall|x: int| #[trigger] result.contains(x) ==> original.contains(x)
}

spec fn contains_all_positives(result: Seq<int>, original: Seq<int>) -> bool {
    forall|i: int| 0 <= i < original.len() && is_positive(original[i]) ==> result.contains(#[trigger] original[i])
}

spec fn preserves_order(result: Seq<int>, original: Seq<int>) -> bool {
    forall|i: int, j: int| 0 <= i < j < result.len() ==> 
        (exists|k1: int, k2: int| 0 <= k1 < k2 < original.len() && original[k1] == #[trigger] result[i] && original[k2] == #[trigger] result[j] &&
        forall|k: int| k1 < k < k2 ==> !is_positive(#[trigger] original[k]))
}

spec fn count_positives(s: Seq<int>) -> int {
    s.len() as int
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): Simplified to use vstd's filter for easier proofs */
spec fn filter_positive(s: Seq<int>) -> Seq<int> {
    s.filter(|x: int| x > 0)
}

/* helper modified by LLM (iteration 3): Added lemma for order preservation using vstd */
proof fn lemma_filter_preserves_order(s: Seq<int>)
    ensures preserves_order(s.filter(|x: int| x > 0), s),
{
    vstd::seq_lib::lemma_filter_preserves_order(s, |x: int| x > 0);
}
// </vc-helpers>

// <vc-spec>
fn get_positive(l: Vec<i8>) -> (result: Vec<i8>)
    ensures 
        all_positive(result@.map(|i: int, x: i8| x as int)),
        all_elements_from_original(result@.map(|i: int, x: i8| x as int), l@.map(|i: int, x: i8| x as int)),
        contains_all_positives(result@.map(|i: int, x: i8| x as int), l@.map(|i: int, x: i8| x as int)),
        result.len() == count_positives(l@.map(|i: int, x: i8| x as int)),
        preserves_order(result@.map(|i: int, x: i8| x as int), l@.map(|i: int, x: i8| x as int)),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): fixed syntax and added proofs for loop invariant and postconditions */
{
    let mut result: Vec<i8> = Vec::new();
    let mut i: usize = 0;
    while i < l.len()
        invariant
            0 <= i <= l.len(),
            result@.map(|_idx: int, x: i8| x as int) == filter_positive(l@.subrange(0, i as int).map(|_idx: int, x: i8| x as int)),
    {
        let x = l[i];
        proof {
            let l_sub_i_map = l@.subrange(0, i as int).map(|_idx, e: i8| e as int);
            vstd::seq_lib::lemma_subrange_and_push(l@, i as int);
            vstd::seq_lib::lemma_map_push(l@.subrange(0, i as int), |_, e: i8| e as int, x);
            vstd::seq_lib::lemma_filter_push(l_sub_i_map, |y: int| y > 0, x as int);
        }

        if x > 0 {
            result.push(x);
        }
        i = i + 1;
    }

    let ghost l_int = l@.map(|_idx: int, x: i8| x as int);
    assert(result@.map(|_idx: int, x: i8| x as int) == filter_positive(l_int));
    
    vstd::seq_lib::lemma_filter_properties(l_int, |x: int| x > 0);
    lemma_filter_preserves_order(l_int);
    
    result
}
// </vc-code>


}

fn main() {}