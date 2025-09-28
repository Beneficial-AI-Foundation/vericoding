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
/* helper modified by LLM (iteration 5): relate i8 positivity to spec is_positive */
proof fn i8_positive_equiv(x: i8) {
    if x as int > 0 {
        assert(is_positive(x as int));
    } else {
        assert(!is_positive(x as int));
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
    /* code modified by LLM (iteration 5): filter positive i8 values into result_vec and maintain invariants without Seq.contains */
    let mut result_vec: Vec<i8> = Vec::new();
    let mut idx: usize = 0;
    let n: usize = l.len();

    while idx < n
        invariant
            forall|i: int| 0 <= i < result_vec@.len() ==> is_positive(result_vec@.map(|j: int, x: i8| x as int)@[i]),
            forall|i: int| 0 <= i < result_vec@.len() ==> (exists|k: int| 0 <= k < l@.len() && l@.map(|j: int, y: i8| y as int)@[k] == result_vec@.map(|j: int, z: i8| z as int)@[i]),
            forall|k: int| 0 <= k < idx as int ==> (l@.map(|j: int, y: i8| y as int)@[k] > 0 ==> (exists|t: int| 0 <= t < result_vec@.len() && result_vec@.map(|j: int, z: i8| z as int)@[t] == l@.map(|j: int, y: i8| y as int)@[k])),
        decreases
            (n as int) - (idx as int)
    {
        let cur: i8 = l[idx];
        if (cur as int) > 0 {
            result_vec.push(cur);
        }
        idx = idx + 1;
    }

    result_vec
}
// </vc-code>


}

fn main() {}