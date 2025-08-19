use vstd::prelude::*;

verus! {
    
    fn main() {
       }

    //SPEC
    fn transpose<T: Copy>(arr: Vec<Vec<T>>) -> (ret: Vec<Vec<T>>)
    ensures 
        ret.len() == arr[0].len(),
        forall|i: int| 0 <= i < ret.len() ==> ret@[i].len() == arr.len(),
        forall|i: int, j: int| 0 <= i < arr.len() && 0 <= j < arr[i].len() ==> ret[j][i] == arr[i][j]
    {
        let rows = arr.len();
        let cols = arr[0].len();
        let mut ret: Vec<Vec<T>> = Vec::new();
        let mut j: usize = 0;
        
        while j < cols
        invariant 
            j <= cols,
            ret.len() == j,
            forall|k: int| 0 <= k < j ==> ret[k].len() == rows,
            forall|k: int, l: int| 0 <= k < rows && 0 <= l < j ==> ret[l][k] == arr[k][l]
        decreases cols - j,
        {
            let mut new_row: Vec<T> = Vec::new();
            let mut i: usize = 0;
            
            while i < rows
            invariant 
                i <= rows,
                new_row.len() == i,
                forall|k: int| 0 <= k < i ==> new_row[k] == arr[k][j as int]
            decreases rows - i,
            {
                new_row.push(arr[i][j]);
                i = i + 1;
            }
            
            ret.push(new_row);
            j = j + 1;
        }
        
        ret
    }
} 