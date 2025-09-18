// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed lemma syntax error by adding exclamation mark */
proof fn count_true_index_lemma(condition: Seq<bool>, i: int) 
    requires 0 <= i < condition.len()
    ensures count_true(condition) == (
        if condition[i] { 1 } else { 0 }
        ) + count_true(condition.take(i)) + count_true(condition.skip(i+1))
{
    if condition.len() == 0 {
        // Base case: empty sequence
    } else if i == 0 {
        // Base case: first element
    } else {
        // Recursive case
        count_true_index_lemma(condition.skip(1), i-1);
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
{
    /* code modified by LLM (iteration 5): Fixed compilation error by replacing Vec::new() with Vec::new(0) */
    let mut result = Vec::new(0);
    let mut index_map = Vec::new(0);
    let mut i: nat = 0;
    
    while i < a.len()
        invariant
            i <= a.len(),
            result.len() == index_map.len(),
            result.len() == count_true(condition@.take(i)),
            forall|k: int| 0 <= k < index_map.len() ==> 
                0 <= index_map@[k] < i && condition@[index_map@[k]] == true,
            forall|k: int| 0 <= k < result.len() ==> 
                result@[k] == a@[index_map@[k]],
            forall|k1: int, k2: int| 0 <= k1 < k2 < index_map.len() ==> 
                index_map@[k1] < index_map@[k2]
        decreases a.len() - i
    {
        if condition[i] {
            result.push(a[i]);
            index_map.push(i as int);
        }
        i += 1;
    }
    (result)
}
// </vc-code>

}
fn main() {}