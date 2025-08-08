use vstd::prelude::*;

verus! {

fn ravel<T: Copy>(arr: &Vec<Vec<T>>) -> (ret: Vec<T>)
    requires 
        arr.len() > 0,
        forall|i: int| 0 <= i < arr.len() ==> #[trigger] arr[i].len() == arr[0].len(),
    ensures 
        ret.len() == arr.len() * arr[0].len(),
        forall|i: int, j: int| 
            0 <= i < arr.len() && 0 <= j < arr[0].len() ==> 
            ret[#[trigger] (i * arr[0].len() + j)] == arr[i][j],
{
    assume(false); // specification only
    Vec::new()
}

fn main() {}

}