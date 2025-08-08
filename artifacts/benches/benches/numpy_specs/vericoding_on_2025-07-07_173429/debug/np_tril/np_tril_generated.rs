use vstd::prelude::*;

verus! {

#[verifier::exec_allows_no_decreases_clause]
#[verifier::external_body]
fn tril(arr: Vec<Vec<i32>>, k: i32) -> (ret: Vec<Vec<i32>>)
    requires 
        arr.len() > 0,
        forall|i: int| 0 <= i < arr.len() ==> #[trigger] arr[i].len() == arr[0].len(),
        arr[0].len() > 0,
    ensures 
        ret.len() == arr.len(),
        forall|i: int| 0 <= i < ret.len() ==> #[trigger] ret[i].len() == arr[0].len(),
        forall|i: int, j: int| 
            0 <= i < arr.len() && 0 <= j < arr[0].len() ==> 
            if j - i > k { ret[i][j] == 0 } else { ret[i][j] == arr[i][j] },
{
    let mut ret: Vec<Vec<i32>> = Vec::new();
    
    for i in 0..arr.len() {
        let mut row: Vec<i32> = Vec::new();
        
        for j in 0..arr[0].len() {
            if j > i && (j - i) as i32 > k {
                row.push(0);
            } else {
                row.push(arr[i][j]);
            }
        }
        
        ret.push(row);
    }
    
    ret
}

fn main() {}

}