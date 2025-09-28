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
/* helper modified by LLM (iteration 5): correct the spec fn with decreases */
spec fn count_positives(s: Seq<int>) -> int
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else if is_positive(s[0]) {
        1 + count_positives(s.drop_first())
    } else {
        count_positives(s.drop_first())
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
    /* code modified by LLM (iteration 5): implement loop to filter positives */
    let mut result: Vec<i8> = Vec::new();
    let mut i = 0usize;
    while i < l.len()
        invariant
            0 <= i <= l.len(),
            result.len() <= i,
            forall|k: int| 0 <= k < result@.len() ==> result@[k] as int > 0,
            forall|k: int| 0 <= k < result@.len() ==> (exists|j: int| 0 <= j < i && l@[j] == result@[k])
        decreases l.len() - i
    {
        if l@[i as int] as int > 0 {
            result.push(l@[i as int]);
        }
        i += 1;
    }
    result
}
// </vc-code>


}

fn main() {}