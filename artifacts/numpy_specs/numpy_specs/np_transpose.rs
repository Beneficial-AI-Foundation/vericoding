use vstd::prelude::*;

verus! {

// SPEC  
fn transpose<T>(arr: Vec<Vec<T>>) -> (ret: Vec<Vec<T>>)
    requires 
        arr.len() > 0,
        forall|i: int| 0 <= i < arr.len() ==> #[trigger] arr[i].len() == arr[0].len(),
    ensures 
        ret.len() == arr[0].len(),
        ret.len() > 0 ==> ret[0].len() == arr.len(),
        forall|i: int, j: int| 0 <= i < arr.len() && 0 <= j < arr[0].len() ==> 
            #[trigger] ret[j][i] == #[trigger] arr[i][j],
{
    assume(false);
    Vec::new()
}

}