use vstd::prelude::*;

verus! {

fn transpose<T: Copy>(arr: Vec<Vec<T>>) -> (ret: Vec<Vec<T>>)
    requires 
        arr.len() > 0,
        forall|i: int| 0 <= i < arr.len() ==> #[trigger] arr[i].len() == arr[0].len(),
    ensures
        ret.len() == arr[0].len(),
        ret.len() > 0 ==> ret[0].len() == arr.len(),
        forall|i: int, j: int| 
            0 <= i < arr.len() && 0 <= j < arr[0].len() ==> 
            ret[j as int][i as int] == arr[i as int][j as int],
{
    let rows = arr.len();
    let cols = arr[0].len();
    
    let mut ret: Vec<Vec<T>> = Vec::new();
    
    let mut j: usize = 0;
    while j < cols
        invariant
            j <= cols,
            ret.len() == j,
            rows == arr.len(),
            cols == arr[0].len(),
            forall|i: int| 0 <= i < arr.len() ==> #[trigger] arr[i].len() == cols,
            forall|k: int| 0 <= k < ret.len() ==> #[trigger] ret[k].len() == rows,
            forall|i: int, j_idx: int| 
                0 <= i < rows && 0 <= j_idx < ret.len() ==> 
                ret[j_idx as int][i as int] == arr[i as int][j_idx as int],
        decreases cols - j,
    {
        let mut row: Vec<T> = Vec::new();
        
        let mut i: usize = 0;
        while i < rows
            invariant
                i <= rows,
                row.len() == i,
                j < cols,
                rows == arr.len(),
                cols == arr[0].len(),
                forall|i_idx: int| 
                    0 <= i_idx < row.len() ==> 
                    #[trigger] row[i_idx] == arr[i_idx][j as int],
                forall|k: int| 0 <= k < arr.len() ==> #[trigger] arr[k].len() == cols,
            decreases rows - i,
        {
            assert(i < arr.len());
            assert(j < arr[i as int].len());
            row.push(arr[i][j]);
            i = i + 1;
        }
        
        ret.push(row);
        j = j + 1;
    }
    
    ret
}

fn main() {}

}