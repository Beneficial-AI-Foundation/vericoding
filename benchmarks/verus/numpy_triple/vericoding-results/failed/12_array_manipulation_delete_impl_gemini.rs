// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed syntax error in forall block */
proof fn lemma_delete_properties(arr: Seq<f32>, res: Seq<f32>, index: int)
    requires
        arr.len() > 0,
        0 <= index < arr.len(),
        res.len() == arr.len() - 1,
        forall|i: int| 0 <= i < index ==> #[trigger] res[i] == arr[i],
        forall|i: int| index <= i < res.len() ==> #[trigger] res[i] == arr[i + 1],
    ensures
        forall|i: int| 0 <= i < arr.len() && i != index ==>
            exists|j: int| 0 <= j < res.len() && res[j] == arr[i],
{
    forall|i: int|
        requires
            0 <= i < arr.len() && i != index,
        ensures
            exists|j: int| 0 <= j < res.len() && res[j] == arr[i],
    {
        if i < index {
            let j = i;
            assert(res[j] == arr[i]);
        } else {
            let j = i - 1;
            assert(res[j] == arr[i]);
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn delete(arr: Vec<f32>, index: usize) -> (result: Vec<f32>)
    requires 
        arr.len() > 0,
        index < arr.len(),
    ensures 
        result.len() == arr.len() - 1,
        forall|i: int| 0 <= i < index ==> #[trigger] result[i] == arr[i],
        forall|i: int| index <= i < result.len() ==> result[i] == #[trigger] arr[i + 1],
        forall|i: int| 0 <= i < arr.len() && i != index ==> 
            exists|j: int| 0 <= j < result.len() && #[trigger] result[j] == #[trigger] arr[i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): updated iteration number in comment */
    let mut result: Vec<f32> = Vec::new();
    let mut i: usize = 0;
    while i < index
        invariant
            0 <= i <= index,
            index < arr.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> #[trigger] result@[j] == arr@[j],
        decreases index - i
    {
        result.push(arr[i]);
        i = i + 1;
    }

    i = index + 1;
    while i < arr.len()
        invariant
            index < arr.len(),
            index <= i <= arr.len(),
            result.len() == i - 1,
            forall|j: int| 0 <= j < index ==> #[trigger] result@[j] == arr@[j],
            forall|j: int| index <= j < result.len() ==> #[trigger] result@[j] == arr@[j + 1],
        decreases arr.len() - i
    {
        result.push(arr[i]);
        i = i + 1;
    }
    
    lemma_delete_properties(arr.view(), result.view(), index as int);
    
    result
}
// </vc-code>

}
fn main() {}