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
/* helper modified by LLM (iteration 5): none */

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
/* code modified by LLM (iteration 5): fix type casting issues from i8 to int for expressions within data types used at runtime */
{
    let mut result: Vec<i8> = Vec::new();
    let mut i: nat = 0;

    while i < l.len()
        invariant
            0 <= i && i <= l.len(),
            result.len() <= i,
            // All elements currently in `result` are positive
            forall|j: int| 0 <= j < result.len() ==> is_positive(result@[j] as int),
            // All elements currently in `result` were originally in `l`
            forall|j: int| 0 <= j < result.len() ==> l@.contains(result@[j]),
            // `result` contains all positive elements encountered so far in `l`
            forall|j: int| 0 <= j < i && is_positive(l@[j] as int) ==> result@.contains(l@[j]),
            // The length of `result` equals the count of positive elements in `l` up to index `i`
            result.len() == (0..i).filter(|k| is_positive(l@[k as int] as int)).count(),
            // The order of elements in `result` is preserved from `l`
            forall|k1: int, k2: int| 0 <= k1 < k2 < result.len() ==> 
                (exists|idx1: int, idx2: int| 
                    0 <= idx1 < idx2 < i && 
                    l@[idx1] == result@[k1] && 
                    l@[idx2] == result@[k2] &&
                    is_positive(l@[idx1] as int) && is_positive(l@[idx2] as int) &&
                    (forall|idx_intermediate: int|
                        idx1 < idx_intermediate < idx2
                        ==> !is_positive(l@[idx_intermediate] as int))
                ),

        decreases l.len() - i
    {
        proof {
            if i < l.len() as int {
                ::vstd::seq::builtin_seq_lib::lemma_len_of_filter_range_plus_1(l@, 0, i as int, i as int + 1, |x: int| is_positive(l@[x as int] as int));
                if is_positive(l@[i as int] as int) {
                    assert((0..(i+1) as int).filter(|k| is_positive(l@[k as int] as int)).count() == result.len() as int + 1);
                } else {
                    assert((0..(i+1) as int).filter(|k| is_positive(l@[k as int] as int)).count() == result.len() as int);
                }
            }
        }

        let current_val: i8 = l[i as int];
        if is_positive(current_val as int) {
            result.push(l[i as int]);
        }
        i = i + 1;
    }
    result
}
// </vc-code>


}

fn main() {}