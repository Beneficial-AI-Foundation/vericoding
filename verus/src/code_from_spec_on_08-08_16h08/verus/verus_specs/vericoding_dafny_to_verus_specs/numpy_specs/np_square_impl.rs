use vstd::prelude::*;

verus! {

fn square(arr: &[i32]) -> (ret: Vec<i32>)
    ensures
        ret.len() == arr.len(),
        forall|i: int| 0 <= i < arr.len() ==> ret[i] == arr[i] * arr[i],
{
    let mut result = Vec::new();
    let mut idx = 0;
    
    /* code modified by LLM (iteration 1): added decreases clause to prove loop termination */
    while idx < arr.len()
        invariant
            result.len() == idx,
            forall|i: int| 0 <= i < idx ==> result[i] == arr[i] * arr[i],
        decreases arr.len() - idx
    {
        let squared = arr[idx] * arr[idx];
        result.push(squared);
        idx += 1;
    }
    
    result
}

}

fn main() {
}