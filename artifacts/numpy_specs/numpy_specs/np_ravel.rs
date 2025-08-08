use vstd::prelude::*;

verus! {

// SPEC
fn ravel<T>(arr: &Vec<Vec<T>>) -> (ret: Vec<T>)
    requires 
        arr.len() > 0,
        forall|i: int| 0 <= i < arr.len() ==> (#[trigger] arr[i]).len() == arr[0].len(),
    ensures 
        ret.len() == arr.len() * arr[0].len(),
        forall|i: int, j: int| 
            0 <= i < arr.len() && 0 <= j < arr[0].len() ==> 
            ret[i * arr[0].len() + j] == arr[i][j],
{
    proof {
        admit();
    }
    Vec::new()
}

}

fn main() {}