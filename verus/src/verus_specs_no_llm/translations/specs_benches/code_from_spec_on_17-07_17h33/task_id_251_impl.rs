use vstd::prelude::*;

verus! {

//IMPL insert_before_each
/* code modified by LLM (iteration 1): Fixed function signature syntax and placement of ensures clause */
fn insert_before_each(arr: &Vec<i32>, elem: i32) -> (result: Vec<i32>)
    ensures
        result@.len() == (2 * arr.len()),
        forall|k: int| 0 <= k < arr.len() ==> #[trigger] result[2 * k] == elem,
        forall|k: int| 0 <= k < arr.len() ==> #[trigger] result[2 * k + 1] == arr[k],
{
    /* code modified by LLM (iteration 1): Implemented function body with proper loop and invariants */
    let mut result = Vec::new();
    let mut i = 0;
    
    /* code modified by LLM (iteration 2): Added decreases clause to prove loop termination */
    while i < arr.len()
        invariant
            i <= arr.len(),
            result@.len() == 2 * i,
            forall|k: int| 0 <= k < i ==> #[trigger] result[2 * k] == elem,
            forall|k: int| 0 <= k < i ==> #[trigger] result[2 * k + 1] == arr[k],
        decreases arr.len() - i
    {
        result.push(elem);
        result.push(arr[i]);
        i += 1;
    }
    
    result
}

} // verus!

fn main() {}