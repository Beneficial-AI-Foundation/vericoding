use vstd::prelude::*;

verus! {

fn tril(arr: &Vec<Vec<i32>>, k: i32) -> (ret: Vec<Vec<i32>>) 
{
    let mut result = Vec::new();
    
    for i in 0..arr.len() {
        let mut row = Vec::new();
        if i < arr.len() {
            for j in 0..arr[i].len() {
                if j <= (i as i32 + k) && (i as i32 + k) >= 0 && j < arr[i].len() {
                    row.push(arr[i][j]);
                } else {
                    row.push(0);
                }
            }
        }
        result.push(row);
    }
    
    result
}

fn main() {}

}