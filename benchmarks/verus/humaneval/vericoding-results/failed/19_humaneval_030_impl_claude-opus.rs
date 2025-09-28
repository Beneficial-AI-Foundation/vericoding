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
/* helper modified by LLM (iteration 5): Added proper count_positives implementation */
spec fn count_positives_impl(s: Seq<int>) -> nat
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else {
        let rest_count = count_positives_impl(s.subrange(0, s.len() - 1));
        if is_positive(s[s.len() - 1]) {
            rest_count + 1
        } else {
            rest_count
        }
    }
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
{
    /* code modified by LLM (iteration 5): Fixed trigger annotation in invariant */
    let mut result = Vec::new();
    let mut i = 0;
    
    while i < l.len()
        invariant
            0 <= i <= l.len(),
            forall|j: int| 0 <= j < result.len() ==> is_positive(result@[j] as int),
            forall|j: int| 0 <= j < result.len() ==> exists|k: int| 0 <= k < l.len() && #[trigger] result@[j] == l@[k],
            forall|k: int| 0 <= k < i && is_positive(l@[k] as int) ==> exists|j: int| 0 <= j < result.len() && result@[j] == l@[k],
            forall|idx1: int, idx2: int| 0 <= idx1 < idx2 < result.len() ==>
                exists|k1: int, k2: int| 0 <= k1 < k2 < i && 
                    l@[k1] == result@[idx1] && 
                    l@[k2] == result@[idx2] &&
                    forall|k: int| k1 < k < k2 ==> !is_positive(l@[k] as int),
        decreases l.len() - i
    {
        if l[i] > 0 {
            result.push(l[i]);
        }
        i = i + 1;
    }
    
    proof {
        assert(all_positive(result@.map(|j: int, x: i8| x as int))) by {
            assert forall|j: int| 0 <= j < result.len() implies is_positive(#[trigger](result@.map(|k: int, x: i8| x as int)[j])) by {
                assert(result@.map(|k: int, x: i8| x as int)[j] == result@[j] as int);
            }
        }
        assert(all_elements_from_original(result@.map(|j: int, x: i8| x as int), l@.map(|j: int, x: i8| x as int))) by {
            assert forall|x: int| #[trigger] (result@.map(|j: int, v: i8| v as int).contains(x)) implies l@.map(|j: int, v: i8| v as int).contains(x) by {
                if result@.map(|j: int, v: i8| v as int).contains(x) {
                    let idx = choose|j: int| 0 <= j < result.len() && result@[j] as int == x;
                    let k = choose|k: int| 0 <= k < l.len() && result@[idx] == l@[k];
                    assert(l@[k] as int == x);
                }
            }
        }
        assert(contains_all_positives(result@.map(|j: int, x: i8| x as int), l@.map(|j: int, x: i8| x as int)));
        assert(preserves_order(result@.map(|j: int, x: i8| x as int), l@.map(|j: int, x: i8| x as int)));
    }
    
    result
}
// </vc-code>


}

fn main() {}