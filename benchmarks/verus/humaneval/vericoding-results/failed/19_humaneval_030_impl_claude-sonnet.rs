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
/* helper modified by LLM (iteration 5): fixed type mismatches for indexing and parameters */
fn lemma_positive_preservation(v: Vec<i8>, i: usize)
    requires
        i < v.len(),
        v@[i as int] > 0,
    ensures
        is_positive(v@[i as int] as int),
{
}

fn lemma_result_properties(result: Vec<i8>, original: Vec<i8>)
    requires
        forall|i: int| 0 <= i < result.len() ==> result@[i] > 0,
        forall|i: int| 0 <= i < result.len() ==> exists|j: int| 0 <= j < original.len() && original@[j] == result@[i],
    ensures
        all_positive(result@.map(|i: int, x: i8| x as int)),
        all_elements_from_original(result@.map(|i: int, x: i8| x as int), original@.map(|i: int, x: i8| x as int)),
{
}

spec fn count_positives_up_to(s: Seq<i8>, n: int) -> int
    decreases n,
{
    if n <= 0 {
        0
    } else if n > s.len() {
        count_positives_up_to(s, s.len())
    } else if is_positive(s[n-1] as int) {
        count_positives_up_to(s, n-1) + 1
    } else {
        count_positives_up_to(s, n-1)
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
    /* code modified by LLM (iteration 5): fixed indexing and parameter type mismatches */
    let mut result = Vec::new();
    let mut i = 0;
    
    while i < l.len()
        invariant
            0 <= i <= l.len(),
            all_positive(result@.map(|i: int, x: i8| x as int)),
            all_elements_from_original(result@.map(|i: int, x: i8| x as int), l@.map(|i: int, x: i8| x as int)),
            contains_all_positives(result@.map(|i: int, x: i8| x as int), l@.subrange(0, i as int).map(|i: int, x: i8| x as int)),
            result.len() == count_positives_up_to(l@, i as int),
        decreases l.len() - i,
    {
        if l@[i as int] > 0 {
            proof {
                lemma_positive_preservation(l, i);
            }
            result.push(l@[i as int]);
        }
        i += 1;
    }
    
    proof {
        lemma_result_properties(result, l);
        assert(count_positives_up_to(l@, l@.len()) == count_positives(l@.map(|i: int, x: i8| x as int)));
    }
    
    result
}
// </vc-code>


}

fn main() {}