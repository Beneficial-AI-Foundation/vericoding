// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Minor cleanup for lemma_contains_implies_contains. */
proof fn lemma_contains_implies_contains(s1: Seq<i8>, s2: Seq<i8>, val: i8)
    requires
        forall|i: int| 0 <= i < s1.len() ==> exists|j: int| 0 <= j < s2.len() && s2.index(j) == s1.index(i),
        exists|k: int| 0 <= k < s1.len() && s1.index(k) == val,
    ensures
        exists|k: int| 0 <= k < s2.len() && s2.index(k) == val,
{
    let k = choose|k: int| 0 <= k < s1.len() && s1.index(k) == val;
    let j = choose|j: int| 0 <= j < s2.len() && s2.index(j) == s1.index(k);
    assert(s2.index(j) == val);
}
// </vc-helpers>

// <vc-spec>
fn unique_all(arr: Vec<i8>) -> (ret: Vec<i8>)
    ensures
        ret.len() <= arr.len(),
        forall|i: int| 0 <= i < arr@.len() ==> exists|j: int| 0 <= j < ret@.len() && ret@[j] == #[trigger] arr@[i],
        forall|i: int, j: int| 0 <= i < ret@.len() && 0 <= j < i ==> ret@[i] != ret@[j],
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Cast loop index `i` to `int` for sequence indexing to resolve type mismatch */
{
    let mut result: Vec<i8> = Vec::new();
    let mut seen: Seq<i8> = Seq::empty();

    let mut i = 0;
    while i < arr.len()
        invariant
            0 <= i as int <= arr.len() as int,
            result.len() <= i,
            forall|j: int| 0 <= j < result.len() ==> exists|k: int| 0 <= k < i && arr@.index(k) == #[trigger] result@.index(j),
            forall|j: int| 0 <= j < result.len() ==> seen.contains(result@.index(j)),
            forall|j: int, l: int| 0 <= j < result.len() && 0 <= l < j ==> result@.index(j) != result@.index(l),
            forall|val: i8| seen.contains(val) ==> (exists|k: int| 0 <= k < i && arr@.index(k) == val),
            forall|val: i8| (exists|k: int| 0 <= k < result.len() && result@.index(k) == val) ==> seen.contains(val),
        decreases arr.len() - i
    {
        let current_val = arr@.index(i as int);
        if !seen.contains(current_val) {
            result.push(current_val);
            seen = seen.push(current_val);
        }

        i = i + 1;
    }

    result
}
// </vc-code>


}
fn main() {}