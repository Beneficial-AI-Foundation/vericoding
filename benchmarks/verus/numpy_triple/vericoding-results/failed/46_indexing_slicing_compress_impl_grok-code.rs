// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed ensures to use proper Verus syntax with |ret| for theUnnamed return tuple, removing circular reference */
fn compressed_helper(condition: Seq<bool>, a: Seq<f32>) -> (Seq<f32>, Seq<int>)
    decreases condition.len()
    requires condition.len() == a.len()
    ensures
        |ret: (Seq<f32>, Seq<int>)|
            ret.0.len() == count_true(condition) &&
            ret.1.len() == count_true(condition) &&
            (forall|i: int| 0 <= i < ret.1.len() ==> 
                0 <= ret.1[i] < condition.len() &&
                condition[ret.1[i]] == true) &&
            (forall|i: int| 0 <= i < ret.0.len() ==> 
                ret.0[i] == a[ret.1[i]]) &&
            (forall|i: int, j: int| 0 <= i < j < ret.1.len() ==> 
                ret.1[i] < ret.1[j])
{
    if condition.len() == 0 {
        (Seq::empty(), Seq::empty())
    } else {
        let (rest_result, rest_mapping) = compressed_helper(condition.skip(1), a.skip(1));
        if condition[0] {
            (rest_result.insert(0, a[0]), rest_mapping.map_values(|x: int| x + 1).insert(0, 0))
        } else {
            (rest_result, rest_mapping.map_values(|x: int| x + 1))
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
/* code modified by LLM (iteration 5): Adjusted code to explicitly name the mapping for potential verification needs */
{
    let (result_seq, mapping) = compressed_helper(condition@, a@);
    Vec::from_seq(result_seq)
}
// </vc-code>

}
fn main() {}