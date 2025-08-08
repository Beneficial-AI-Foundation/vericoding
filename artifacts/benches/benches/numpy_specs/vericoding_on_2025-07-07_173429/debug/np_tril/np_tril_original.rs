use vstd::prelude::*;

verus! {

#[verifier(external_body)]
fn tril(arr: &Vec<Vec<i32>>, k: i32) -> (ret: Vec<Vec<i32>>)
    requires 
        arr.len() > 0,
        arr[0].len() > 0,
        forall|i: int| 0 <= i < arr.len() ==> #[trigger] arr[i].len() == arr[0].len(),
        -((arr.len() as i32) - 1) < k < (arr[0].len() as i32) - 1,
    ensures
        ret.len() == arr.len(),
        ret.len() > 0 ==> ret[0].len() == arr[0].len(),
        forall|i: int, j: int| 
            0 <= i < arr.len() && 0 <= j < arr[0].len() ==> 
                if j - i > k { 
                    #[trigger] ret[i][j] == 0 
                } else { 
                    #[trigger] ret[i][j] == arr[i][j] 
                }
{
    // Implementation would go here
    arr.clone() // placeholder
}

fn main() {}

}