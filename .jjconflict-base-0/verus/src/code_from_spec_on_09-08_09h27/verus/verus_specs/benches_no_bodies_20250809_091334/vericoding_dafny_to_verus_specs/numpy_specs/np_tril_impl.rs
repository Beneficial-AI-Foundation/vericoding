use vstd::prelude::*;

verus! {

fn tril(arr: &Vec<Vec<i32>>, k: i32) -> (ret: Vec<Vec<i32>>) 
{
    let mut result = Vec::new();
    
    for i in 0..arr.len() {
        let mut row = Vec::new();
        let current_row = &arr[i];
        
        for j in 0..current_row.len() {
            if (j as i32) <= (i as i32) + k {
                row.push(current_row[j]);
            } else {
                row.push(0);
            }
        }
        result.push(row);
    }
    
    result
}

fn main() {}

}