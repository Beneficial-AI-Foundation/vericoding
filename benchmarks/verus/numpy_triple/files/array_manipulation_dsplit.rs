use vstd::prelude::*;

verus! {

fn dsplit(arr: Vec<f32>, sections: usize) -> (result: Vec<Vec<f32>>)
    requires 
        sections > 0,
        arr.len() % sections == 0,
    ensures
        result.len() == sections,
        forall|i: int| 0 <= i < sections ==> result[i].len() == arr.len() / sections,
        forall|i: int, j: int| 0 <= i < sections && 0 <= j < (arr.len() / sections) ==> 
            result[i][j] == arr[i * (arr.len() / sections) + j],
{
    assume(false);
    unreached()
}

}
fn main() {}