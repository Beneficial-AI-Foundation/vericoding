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
    let mut result = Vec::new();
    let rows = arr.len();
    let cols = arr[0].len();
    
    for i in 0..rows
        invariant
            result.len() == i * cols,
            forall|ii: int, jj: int|
                0 <= ii < i && 0 <= jj < cols ==>
                result[ii * cols + jj] == arr[ii][jj],
    {
        for j in 0..cols
            invariant
                result.len() == i * cols + j,
                forall|ii: int, jj: int|
                    0 <= ii < i && 0 <= jj < cols ==>
                    result[ii * cols + jj] == arr[ii][jj],
                forall|jj: int|
                    0 <= jj < j ==>
                    /* code modified by LLM (iteration 1): Fixed type mismatch by casting j to int */
                    result[i * cols + jj] == arr[i as int][jj],
        {
            result.push(arr[i][j].clone());
        }
    }
    
    result
}

}

fn main() {}