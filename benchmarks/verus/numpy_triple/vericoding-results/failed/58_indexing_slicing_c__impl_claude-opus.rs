// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn c_(arr1: Vec<i8>, arr2: Vec<i8>) -> (result: Vec<Vec<i8>>)
    requires arr1.len() == arr2.len(),
    ensures 
        result.len() == arr1.len(),
        forall|i: int| 0 <= i < result.len() ==> 
            result[i]@.len() == 2 &&
            result[i][0] == arr1[i] &&
            result[i][1] == arr2[i]
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Added assertions to help verifier track result updates */
    let mut result: Vec<Vec<i8>> = Vec::new();
    let mut i: usize = 0;
    while i < arr1.len()
        invariant
            i <= arr1.len(),
            arr1.len() == arr2.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i as int ==> 
                result[j]@.len() == 2 &&
                result[j][0] == arr1[j] &&
                result[j][1] == arr2[j],
        decreases arr1.len() - i
    {
        let mut pair: Vec<i8> = Vec::new();
        pair.push(arr1[i]);
        pair.push(arr2[i]);
        assert(pair@.len() == 2);
        assert(pair[0] == arr1[i as int]);
        assert(pair[1] == arr2[i as int]);
        let old_result_len = result.len();
        result.push(pair);
        assert(result.len() == old_result_len + 1);
        assert(result[old_result_len as int]@.len() == 2);
        assert(result[old_result_len as int][0] == arr1[i as int]);
        assert(result[old_result_len as int][1] == arr2[i as int]);
        assert(forall|j: int| 0 <= j < old_result_len as int ==> result[j]@.len() == 2 && result[j][0] == arr1[j] && result[j][1] == arr2[j]);
        i = i + 1;
        assert(result.len() == i);
        assert(forall|j: int| 0 <= j < i as int ==> result[j]@.len() == 2 && result[j][0] == arr1[j] && result[j][1] == arr2[j]);
    }
    result
}
// </vc-code>

}
fn main() {}