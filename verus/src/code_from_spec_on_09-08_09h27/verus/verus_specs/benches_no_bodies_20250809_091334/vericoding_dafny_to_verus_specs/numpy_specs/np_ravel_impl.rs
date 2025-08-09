use vstd::prelude::*;

verus! {

// SPEC
fn ravel<T: Clone>(arr: &Vec<Vec<T>>) -> (ret: Vec<T>)
    requires 
        arr.len() > 0,
        forall|i: int| 0 <= i < arr.len() ==> (#[trigger] arr[i]).len() == arr[0].len(),
    ensures 
        ret.len() == arr.len() * arr[0].len(),
        forall|i: int, j: int| 
            0 <= i < arr.len() && 0 <= j < arr[0].len() ==> 
            ret[i * arr[0].len() + j] == arr[i][j],
{
    let mut result: Vec<T> = Vec::new();
    let rows = arr.len();
    let cols = arr[0].len();
    
    /* code modified by LLM (iteration 1): Added Clone bound to T and clone values to fix move error */
    for i in 0..rows
        invariant
            result.len() == i * cols,
            forall|r: int, c: int| 
                0 <= r < i && 0 <= c < cols ==> 
                result[r * cols + c] == arr[r][c],
    {
        for j in 0..cols
            invariant
                result.len() == i * cols + j,
                forall|r: int, c: int| 
                    0 <= r < i && 0 <= c < cols ==> 
                    result[r * cols + c] == arr[r][c],
                forall|c: int|
                    0 <= c < j ==>
                    result[i * cols + c] == arr[i as int][c],
        {
            result.push(arr[i][j].clone());
        }
    }
    
    result
}

}

fn main() {}