// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn c_(arr1: Vec<f32>, arr2: Vec<f32>) -> (result: Vec<Vec<f32>>)
    requires arr1.len() == arr2.len(),
    ensures 
        result.len() == arr1.len(),
        forall|i: int| 0 <= i < result.len() ==> 
            result[i].len() == 2 &&
            result[i][0] == arr1[i] &&
            result[i][1] == arr2[i]
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): added proof block to maintain loop invariant after push */
    let mut result: Vec<Vec<f32>> = Vec::new();
    let mut i: usize = 0;
    while i < arr1.len()
        invariant
            arr1.len() == arr2.len(),
            0 <= i <= arr1.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> 
                result@[j].len() == 2 &&
                result@[j][0] == arr1@[j] &&
                result@[j][1] == arr2@[j]
        decreases arr1.len() - i
    {
        let mut inner_vec: Vec<f32> = Vec::new();
        inner_vec.push(arr1[i]);
        inner_vec.push(arr2[i]);
        
        let ghost old_result_seq = result@;
        result.push(inner_vec);

        proof {
            // Assert property for new element
            assert(inner_vec@.len() == 2 && inner_vec@[0] == arr1[i as int] && inner_vec@[1] == arr2[i as int]);
            assert(result@[i as int] =~= inner_vec@);

            // Assert prefix is unchanged, which allows Verus to carry over the invariant
            assert(result@.subrange(0, i as int) =~= old_result_seq);
        }

        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}