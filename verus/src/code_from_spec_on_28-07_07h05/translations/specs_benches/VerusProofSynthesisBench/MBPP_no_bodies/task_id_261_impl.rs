use vstd::prelude::*;

verus! {

fn element_wise_division(arr1: &Vec<u32>, arr2: &Vec<u32>) -> (result: Vec<u32>)
    // pre-conditions-start
    requires
        arr1.len() == arr2.len(),
        forall|i: int| 0 <= i < arr2.len() ==> arr2[i] != 0,
        forall|m: int|
            0 <= m < arr1.len() ==> (u32::MIN <= #[trigger] arr1[m] / #[trigger] arr2[m]
                <= u32::MAX),
    // pre-conditions-end
    // post-conditions-start
    ensures
        result.len() == arr1.len(),
        forall|i: int|
            0 <= i < result.len() ==> #[trigger] result[i] == #[trigger] (arr1[i] / arr2[i]),
    // post-conditions-end
{
    let mut result = Vec::new();
    let mut i: usize = 0;
    
    /* code modified by LLM (iteration 1): fixed loop invariant and added proper bounds checking */
    while i < arr1.len()
        invariant
            i <= arr1.len(),
            arr1.len() == arr2.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> #[trigger] result[j] == #[trigger] (arr1[j] / arr2[j]),
            forall|k: int| 0 <= k < arr2.len() ==> arr2[k] != 0,
        decreases arr1.len() - i
    {
        /* code modified by LLM (iteration 1): added assertions to prove division safety and bounds */
        assert(i < arr1.len());
        assert(arr1.len() == arr2.len());
        assert(i < arr2.len());
        assert(arr2[i as int] != 0);
        
        let quotient = arr1[i] / arr2[i];
        result.push(quotient);
        i += 1;
    }
    
    result
}

} // verus!

fn main() {}