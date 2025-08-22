use vstd::prelude::*;

verus! {

fn insert_before_each(arr: &Vec<i32>, elem: i32) -> (result: Vec<i32>)
    // post-conditions-start
    ensures
        result@.len() == (2 * arr.len()),
        forall|k: int| 0 <= k < arr.len() ==> #[trigger] result[2 * k] == elem,
        forall|k: int| 0 <= k < arr.len() ==> #[trigger] result[2 * k + 1] == arr[k],
    // post-conditions-end
{
    let mut result = Vec::new();
    let mut i = 0;
    
    /* code modified by LLM (iteration 1): added decreases clause and strengthened invariant to help prove postcondition */
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            result@.len() == 2 * i,
            forall|k: int| 0 <= k < i ==> #[trigger] result[2 * k] == elem,
            forall|k: int| 0 <= k < i ==> #[trigger] result[2 * k + 1] == arr[k],
        decreases arr.len() - i
    {
        result.push(elem);
        result.push(arr[i]);
        i += 1;
    }
    
    /* code modified by LLM (iteration 1): added assertion to help prove postcondition */
    assert(i == arr.len());
    assert(result@.len() == 2 * i);
    
    result
}

} // verus!

fn main() {}