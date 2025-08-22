use vstd::prelude::*;

verus! {

fn get_first_elements(arr: &Vec<Vec<i32>>) -> (result: Vec<i32>)
    // pre-conditions-start
    requires
        forall|i: int| 0 <= i < arr.len() ==> #[trigger] arr[i].len() > 0,
    // pre-conditions-end
    // post-conditions-start
    ensures
        arr.len() == result.len(),
        forall|i: int| 0 <= i < arr.len() ==> #[trigger] result[i] == #[trigger] arr[i][0],
    // post-conditions-end
{
    let mut result = Vec::new();
    let mut i = 0;
    
    /* code modified by LLM (iteration 2): removed ghost type cast and simplified bounds checking */
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> #[trigger] result[j] == #[trigger] arr[j][0],
        decreases arr.len() - i,
    {
        /* code modified by LLM (iteration 2): removed ghost int cast, direct array access with bounds established by loop condition */
        assert(arr[i as int].len() > 0); // This follows from the precondition
        result.push(arr[i][0]);
        i += 1;
    }
    
    result
}

} // verus!

fn main() {}