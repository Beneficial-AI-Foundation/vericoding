// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn preserve_order_lemma(lst: Seq<nat>, result: Seq<nat>, target: nat)
    ensures
        forall|i: int, j: int| 0 <= i < j < lst.len() && lst[i] != target && lst[j] != target ==>
            exists|k1: int, k2: int| 0 <= k1 < k2 < result.len() &&
            result[k1] == lst[i] && result[k2] == lst[j]
{
    /* helper modified by LLM (iteration 5): Fixed assert_by syntax error */
    assert_by(forall|i: int, j: int| 0 <= i < j < lst.len() && lst[i] != target && lst[j] != target ==> 
        exists|k1: int, k2: int| 0 <= k1 < k2 < result.len() && result[k1] == lst[i] && result[k2] == lst[j], ());
}
// </vc-helpers>

// <vc-spec>
fn remove_element(lst: &Vec<nat>, target: nat) -> (result: Vec<nat>)
    ensures
        forall|i: int| 0 <= i < result.len() ==> #[trigger] result[i] != target,
        forall|i: int| 0 <= i < result.len() ==> 
            exists|j: int| 0 <= j < lst.len() && #[trigger] lst[j] == #[trigger] result[i] && lst[j] != target,
        forall|i: int, j: int| 0 <= i < j < lst.len() && lst[i] != target && lst[j] != target ==> 
            exists|k1: int, k2: int| 0 <= k1 < k2 < result.len() && 
            result[k1] == lst[i] && result[k2] == lst[j],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed verification errors */
    let mut result_vec = Vec::new();
    let mut index: usize = 0;
    
    while index < lst.len()
        invariant
            result_vec@.len() <= index as int,
            forall|i: int| 0 <= i < result_vec@.len() ==> result_vec@[i] != target,
            forall|i: int| 0 <= i < result_vec@.len() ==> 
                exists|j: int| 0 <= j < index as int && lst[j] == result_vec@[i] && lst[j] != target,
            forall|i: int, j: int| 0 <= i < j < index as int && lst[i] != target && lst[j] != target ==> 
                exists|k1: int, k2: int| 0 <= k1 < k2 < result_vec@.len() && 
                result_vec@[k1] == lst[i] && result_vec@[k2] == lst[j]
        decreases lst.len() - index
    {
        let elem = lst[index];
        if elem != target {
            result_vec.push(elem);
            proof {
                let result_vec_seq = result_vec@;
                let len = result_vec_seq.len() - 1;
                assert(result_vec_seq[len] == elem);
                assert(result_vec_seq[len] != target);
                assert(exists|j: int| j == index as int && lst[j] == result_vec_seq[len] && lst[j] != target);
            }
        }
        index += 1;
    }
    
    result_vec
}
// </vc-code>

}
fn main() {}