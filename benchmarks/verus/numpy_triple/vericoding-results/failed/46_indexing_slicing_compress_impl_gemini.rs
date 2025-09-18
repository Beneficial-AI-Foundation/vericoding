// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): No change to logic, just updating comment. */
proof fn lemma_count_true_snoc(s: Seq<bool>, b: bool)
    ensures count_true(s.push(b)) == count_true(s) + if b { 1int } else { 0int }
    decreases s.len()
{
    if s.len() > 0 {
        lemma_count_true_snoc(s.skip(1), b);
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
/* code modified by LLM (iteration 5): Moved lemma call into proof blocks to fix compilation error. */
{
    let mut result: Vec<f32> = Vec::new();
    let mut i: usize = 0;
    let ghost mut mapping: Seq<int> = Seq::empty();

    while i < a.len()
        invariant
            0 <= i <= a.len(),
            condition.len() == a.len(),
            result.len() as int == count_true(condition@.subrange(0, i as int)),
            mapping.len() as int == result.len() as int,
            forall|k: int| 0 <= k < mapping.len() ==> 
                0 <= mapping[k] < i as int && condition@[mapping[k]],
            forall|k: int| 0 <= k < result.len() ==> 
                result@[k] == a@[mapping[k]],
            forall|k: int, j: int| 0 <= k < j < mapping.len() ==> 
                mapping[k] < mapping[j],
    {
        if condition[i] {
            result.push(a[i]);
            proof {
                lemma_count_true_snoc(condition@.subrange(0, i as int), condition@[i as int]);
                mapping = mapping.push(i as int);
            }
        } else {
            proof {
                lemma_count_true_snoc(condition@.subrange(0, i as int), condition@[i as int]);
            }
        }
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}