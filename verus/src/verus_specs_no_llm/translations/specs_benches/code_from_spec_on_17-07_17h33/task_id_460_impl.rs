use vstd::prelude::*;

verus! {

//IMPL get_first_elements
fn get_first_elements(arr: &Vec<Vec<i32>>) -> (result: Vec<i32>)
{
    return false;  // TODO: Remove this line and implement the function body
}
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
    /* code modified by LLM (iteration 1): Fixed forall syntax, moved requires/ensures to proper position, and implemented function body */
    let mut result = Vec::new();
    let mut i = 0;
    
    while i < arr.len()
        invariant
            i <= arr.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> #[trigger] result[j] == #[trigger] arr[j][0],
    {
        result.push(arr[i][0]);
        i += 1;
    }
    
    result
}

} // verus!

fn main() {}