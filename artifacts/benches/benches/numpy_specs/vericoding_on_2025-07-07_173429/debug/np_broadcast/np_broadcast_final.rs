use vstd::prelude::*;

verus! {

fn broadcast(a: &Vec<i32>, shape: &Vec<usize>) -> (ret: Vec<Vec<i32>>)
    requires 
        shape.len() == 2,
        (shape[0] == a.len() || shape[1] == a.len()),
    ensures 
        ret.len() == shape[0],
        forall|i: int| 0 <= i < shape[0] ==> #[trigger] ret[i].len() == shape[1],
        forall|i: int, j: int| 0 <= i < shape[0] && 0 <= j < shape[1] ==> {
            if shape[0] == a.len() {
                ret[i][j] == a[i]
            } else {
                ret[i][j] == a[j]
            }
        }
{
    let mut ret: Vec<Vec<i32>> = Vec::new();
    
    let rows = shape[0];
    let cols = shape[1];
    
    if rows == a.len() {
        // Broadcast along rows: each row gets the corresponding element from a
        let mut i: usize = 0;
        while i < rows
            invariant 
                i <= rows,
                ret.len() == i,
                rows == a.len(),
                forall|ii: int| 0 <= ii < i ==> #[trigger] ret[ii].len() == cols,
                forall|ii: int, jj: int| 0 <= ii < i && 0 <= jj < cols ==> ret[ii][jj] == a[ii],
            decreases rows - i
        {
            let mut row: Vec<i32> = Vec::new();
            let mut j: usize = 0;
            while j < cols
                invariant 
                    j <= cols,
                    row.len() == j,
                    i < a.len(),
                    forall|jj: int| 0 <= jj < j ==> row[jj] == a[i as int],
                decreases cols - j
            {
                row.push(a[i]);
                j += 1;
            }
            ret.push(row);
            i += 1;
        }
    } else {
        // cols == a.len()
        // Broadcast along columns: each column gets the corresponding element from a  
        let mut i: usize = 0;
        while i < rows
            invariant 
                i <= rows,
                ret.len() == i,
                cols == a.len(),
                forall|ii: int| 0 <= ii < i ==> #[trigger] ret[ii].len() == cols,
                forall|ii: int, jj: int| 0 <= ii < i && 0 <= jj < cols ==> ret[ii][jj] == a[jj],
            decreases rows - i
        {
            let mut row: Vec<i32> = Vec::new();
            let mut j: usize = 0;
            while j < cols
                invariant 
                    j <= cols,
                    row.len() == j,
                    cols == a.len(),
                    forall|jj: int| 0 <= jj < j ==> row[jj] == a[jj],
                decreases cols - j
            {
                row.push(a[j]);
                j += 1;
            }
            ret.push(row);
            i += 1;
        }
    }
    
    ret
}

fn main() {}

}