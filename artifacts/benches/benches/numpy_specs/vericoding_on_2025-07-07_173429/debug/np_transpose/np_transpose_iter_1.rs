use vstd::prelude::*;

verus! {

fn transpose<T: Copy>(arr: &Vec<Vec<T>>) -> (ret: Vec<Vec<T>>)
    requires 
        arr.len() > 0,
        forall|i: int| 0 <= i < arr.len() ==> #[trigger] arr[i].len() == arr[0].len(),
    ensures 
        ret.len() == arr[0].len(),
        forall|i: int| 0 <= i < ret.len() ==> #[trigger] ret[i].len() == arr.len(),
        forall|i: int, j: int| 
            0 <= i < arr.len() && 0 <= j < arr[0].len() ==> 
                ret[j][i] == arr[i][j],
{
    let rows = arr.len();
    let cols = arr[0].len();
    
    let mut ret: Vec<Vec<T>> = Vec::new();
    
    let mut j = 0usize;
    while j < cols
        invariant
            0 <= j <= cols,
            ret.len() == j,
            cols == arr[0].len(),
            rows == arr.len(),
            rows > 0,
            forall|i: int| 0 <= i < arr.len() ==> #[trigger] arr[i].len() == arr[0].len(),
            forall|k: int| 0 <= k < j ==> #[trigger] ret[k].len() == rows,
            forall|i: int, k: int| 
                0 <= i < rows && 0 <= k < j ==> 
                    ret[k][i] == arr[i][k],
        decreases cols - j,
    {
        assert(j < cols);
        assert(cols == arr[0].len());
        assert(j < arr[0].len());
        
        let mut row: Vec<T> = Vec::new();
        let mut i = 0usize;
        
        while i < rows
            invariant
                0 <= i <= rows,
                row.len() == i,
                rows == arr.len(),
                rows > 0,
                j < cols,
                j < arr[0].len(),
                cols == arr[0].len(),
                forall|k: int| 0 <= k < arr.len() ==> #[trigger] arr[k].len() == arr[0].len(),
                forall|k: int| 0 <= k < i ==> #[trigger] row[k] == arr[k][j as int],
            decreases rows - i,
        {
            assert(i < rows);
            assert(rows == arr.len());
            assert(i < arr.len());
            assert(j < arr[0].len());
            // From the precondition: arr[i].len() == arr[0].len()
            assert(j < arr[i as int].len());
            row.push(arr[i][j]);
            i += 1;
        }
        
        ret.push(row);
        j += 1;
    }
    
    ret
}

fn main() {}

}