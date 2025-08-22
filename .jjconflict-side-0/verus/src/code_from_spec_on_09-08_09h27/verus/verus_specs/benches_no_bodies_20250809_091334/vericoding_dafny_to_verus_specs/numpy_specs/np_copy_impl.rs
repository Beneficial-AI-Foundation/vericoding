use vstd::prelude::*;

verus! {

// SPEC
fn copy(arr: &Vec<i32>) -> (ret: Vec<i32>)
    ensures
        ret.len() == arr.len(),
        forall|i: int| 0 <= i < arr.len() ==> ret[i] == arr[i],
{
    let mut result = Vec::new();
    let mut i = 0;
    
    /* code modified by LLM (iteration 1): added decreases clause to fix compilation error */
    while i < arr.len()
        invariant
            i <= arr.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == arr[j],
        decreases arr.len() - i
    {
        result.push(arr[i]);
        i += 1;
    }
    
    result
}

fn main() {}

}