// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed predicate syntax with exclamation mark */
predicate contains(seq: Seq<i32>, elem: i32) {
    exists|i: int| 0 <= i < seq.len() && seq[i] == elem
}

proof fn dedup_inner(s: &Vec<i32>, i: nat, result: Vec<i32>) -> (res: Vec<i32>)
    requires
        i <= s@.len(),
        forall|k: nat, l: nat| k < l < result@.len() ==> result@[k] != result@[l],
        forall|k: nat| k < result@.len() ==> 
            exists|j: nat| j < i && s@[j] == #[trigger] result@[k],
        forall|j: nat| j < i ==> 
            exists|k: nat| k < result@.len() && result@[k] == #[trigger] s@[j],
    ensures
        res@.len() <= s@.len(),
        forall|k: nat, l: nat| k < l < res@.len() ==> res@[k] != res@[l],
        forall|k: nat| k < res@.len() ==> 
            exists|j: nat| j < s@.len() && s@[j] == #[trigger] res@[k],
        forall|j: nat| j < s@.len() ==> 
            exists|k: nat| k < res@.len() && res@[k] == #[trigger] s@[j],
    decreases s@.len() - i,
{
    if i == s@.len() {
        result
    } else {
        let elem = s@[i];
        let found = contains(result@, elem);
        if found {
            dedup_inner(s, i + 1, result)
        } else {
            let mut new_result = result;
            new_result.push(elem);
            dedup_inner(s, i + 1, new_result)
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn set_to_seq(s: &Vec<i32>) -> (result: Vec<i32>)
    ensures

        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] != result[j],

        forall|i: int| 0 <= i < result.len() ==> 
            exists|j: int| 0 <= j < s.len() && s[j] == #[trigger] result[i],

        forall|i: int| 0 <= i < s.len() ==> 
            exists|j: int| 0 <= j < result.len() && result[j] == #[trigger] s[i],
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed ghost code and return value */
{
    let mut result = Vec::new();
    proof {
        let res = dedup_inner(s, 0, result);
        result = res;
    }
    result
}
// </vc-code>

}
fn main() {}