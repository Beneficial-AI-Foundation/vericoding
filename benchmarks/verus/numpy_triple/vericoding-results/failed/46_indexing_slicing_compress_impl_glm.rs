// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): fixed map closure signature */
spec fn get_true_indices(condition: Seq<bool>) -> Seq<int>
    decreases condition.len()
{
    if condition.len() == 0 {
        Seq::empty()
    } else {
        let rest = get_true_indices(condition.skip(1));
        if condition[0] {
            Seq::new(1, |i: int| 0) + rest.map(|_idx: int, i: int| i + 1)
        } else {
            rest.map(|_idx: int, i: int| i + 1)
        }
    }
}

proof fn lemma_get_true_indices(condition: Seq<bool>)
    ensures
        get_true_indices(condition).len() == count_true(condition),
        forall|i: int| 0 <= i < get_true_indices(condition).len() ==> 
            0 <= get_true_indices(condition)[i] < condition.len() && 
            condition[get_true_indices(condition)[i]] == true,
        forall|i: int, j: int| 0 <= i < j < get_true_indices(condition).len() ==> 
            get_true_indices(condition)[i] < get_true_indices(condition)[j]
{
    if condition.len() == 0 {
        // Trivial
    } else {
        let rest = condition.skip(1);
        lemma_get_true_indices(rest);
        if condition[0] {
            assert(get_true_indices(condition).len() == 1 + get_true_indices(rest).len());
            assert(get_true_indices(rest).len() == count_true(rest));
            assert(count_true(condition) == 1 + count_true(rest));
            assert(get_true_indices(condition).len() == count_true(condition));
        } else {
            assert(get_true_indices(condition).len() == get_true_indices(rest).len());
            assert(get_true_indices(rest).len() == count_true(rest));
            assert(count_true(condition) == count_true(rest));
            assert(get_true_indices(condition).len() == count_true(condition));
        }
    }
}
// </vc-helpers>

// <vc-spec>
spec fn count_true(condition: Seq<bool>) -> int
    decreases condition.len()
{
    if condition.len() == 0 {
        0
    } else {
        (if condition[0] { 1int } else { 0int }) + count_true(condition.skip(1))
    }
}

fn compress(condition: Vec<bool>, a: Vec<f32>) -> (result: Vec<f32>)
    requires condition.len() == a.len(),
    ensures
        result.len() == count_true(condition@),
        exists|mapping: Seq<int>|
            mapping.len() == result.len() &&
            (forall|i: int| 0 <= i < mapping.len() ==> 
                0 <= mapping[i] < condition.len() &&
                condition@[mapping[i]] == true) &&
            (forall|i: int| 0 <= i < result.len() ==> 
                result@[i] == a@[mapping[i]]) &&
            (forall|i: int, j: int| 0 <= i < j < mapping.len() ==> 
                mapping[i] < mapping[j]),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): fixed return statement and proof block */
{
    let mut result = Vec::new();
    for i in 0..condition.len() {
        if condition[i] {
            result.push(a[i]);
        }
    }

    proof {
        let mapping = get_true_indices(condition@);
        lemma_get_true_indices(condition@);
        assert(forall|j: int| 0 <= j < mapping.len() ==> result@[j] == a@[mapping[j]]);
    }
    result
}
// </vc-code>

}
fn main() {}