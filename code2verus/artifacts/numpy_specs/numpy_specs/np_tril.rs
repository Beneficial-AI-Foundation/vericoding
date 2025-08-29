use vstd::prelude::*;

verus! {

fn tril(arr: &Vec<Vec<i32>>, k: i32) -> (ret: Vec<Vec<i32>>) 
{
    let mut result: Vec<Vec<i32>> = Vec::new();
    
    for row_idx in 0..arr.len() {
        let mut new_row: Vec<i32> = Vec::new();
        
        if row_idx < arr.len() {
            let cols = arr[row_idx].len();
            for col_idx in 0..cols {
                if row_idx < arr.len() && col_idx < arr[row_idx].len() {
                    let diff = (col_idx as i32).wrapping_sub(row_idx as i32);
                    if diff > k {
                        new_row.push(0);
                    } else {
                        new_row.push(arr[row_idx][col_idx]);
                    }
                }
            }
        }
        
        result.push(new_row);
    }
    
    result
}

fn main() {}

}