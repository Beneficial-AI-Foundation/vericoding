use vstd::prelude::*;

verus! {

fn tril(arr: Vec<Vec<i32>>, k: i32) -> (ret: Vec<Vec<i32>>)
    requires
        arr.len() > 0,
        forall|i: int| 0 <= i < arr.len() ==> #[trigger] arr[i].len() == arr[0].len(),
    ensures
        ret.len() == arr.len(),
        forall|i: int| 0 <= i < ret.len() ==> #[trigger] ret[i].len() == arr[0].len(),
        forall|i: int, j: int| 
            0 <= i < arr.len() && 0 <= j < arr[0].len() ==> 
            (if j - i > (k as int) { ret[i][j] == 0 } else { ret[i][j] == arr[i][j] }),
{
    let mut ret: Vec<Vec<i32>> = Vec::new();
    let rows = arr.len();
    
    if rows == 0 {
        return ret;
    }
    
    let cols = arr[0].len();
    
    for i in 0..rows {
        let mut row: Vec<i32> = Vec::new();
        
        for j in 0..cols {
            if (j as i32) - (i as i32) > k {
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