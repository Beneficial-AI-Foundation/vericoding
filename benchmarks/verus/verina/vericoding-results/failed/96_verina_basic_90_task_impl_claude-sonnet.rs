// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn slope_search_precond(a: &Vec<Vec<i32>>, key: i32) -> bool {
    a.len() > 0 &&
    (forall|i: int| 0 <= i < a.len() ==> #[trigger] a[i].len() == a[0].len()) &&
    (forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < a[i].len() - 1 ==> #[trigger] a[i][j] <= a[i][j + 1]) &&
    (forall|j: int, i: int| 0 <= j < a[0].len() && 0 <= i < a.len() - 1 ==> #[trigger] a[i][j] <= a[i + 1][j])
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): helper function to calculate search space decrease */
spec fn search_space_measure(row: i32, col: i32, rows: int, cols: int) -> int {
    (rows - row as int) + (col as int + 1)
}

/* helper modified by LLM (iteration 5): helper function to check valid indices */
spec fn valid_indices(row: i32, col: i32, rows: int, cols: int) -> bool {
    0 <= row < rows && 0 <= col < cols
}

/* helper modified by LLM (iteration 5): helper lemma for postcondition */
proof fn slope_search_postcondition_lemma(a: &Vec<Vec<i32>>, key: i32, row: i32, col: i32, found_key: bool)
    requires 
        slope_search_precond(a, key),
        0 <= row <= a.len(),
        -1 <= col < a[0].len() as int,
        found_key ==> (0 <= row < a.len() && 0 <= col < a[0].len() && a[row as int][col as int] == key),
        !found_key ==> (forall|i: int| 0 <= i < row ==> #[trigger] (forall|j: int| 0 <= j < a[i].len() ==> a[i][j] < key)),
        !found_key ==> (forall|i: int| 0 <= i < a.len() ==> #[trigger] (forall|j: int| col + 1 <= j < a[i].len() ==> a[i][j] > key)),
        !found_key ==> (row >= a.len() || col < 0)
    ensures
        found_key ==> (row >= 0 && row < a.len() && col >= 0 && col < a[0].len() && a[row as int][col as int] == key),
        !found_key ==> (forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < a[i].len() ==> #[trigger] a[i][j] != key)
{
}
// </vc-helpers>

// <vc-spec>
fn slope_search(a: &Vec<Vec<i32>>, key: i32) -> (result: (i32, i32))
    requires slope_search_precond(a, key),
    ensures
        ({
            let (m, n) = result;
            ((m >= 0 && m < a.len() && n >= 0 && n < a[0].len() && a[m as int][n as int] == key) ||
             (m == -1 && n == -1 && forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < a[i].len() ==> #[trigger] a[i][j] != key))
        })
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed bounds checking and invariant satisfaction */
    if a[0].len() == 0 {
        return (-1, -1);
    }
    
    let mut row = 0i32;
    let mut col = (a[0].len() - 1) as i32;
    
    while row < a.len() as i32 && col >= 0
        invariant
            0 <= row <= a.len(),
            -1 <= col < a[0].len() as int,
            a.len() > 0,
            a[0].len() > 0,
            forall|i: int| 0 <= i < row ==> #[trigger] (forall|j: int| 0 <= j < a[i].len() ==> a[i][j] < key),
            forall|i: int| 0 <= i < a.len() ==> #[trigger] (forall|j: int| col + 1 <= j < a[i].len() ==> a[i][j] > key)
        decreases search_space_measure(row, col, a.len() as int, a[0].len() as int)
    {
        let current = a[row as usize][col as usize];
        
        if current == key {
            return (row, col);
        } else if current < key {
            row += 1;
        } else {
            col -= 1;
        }
    }
    
    proof {
        slope_search_postcondition_lemma(a, key, row, col, false);
    }
    
    (-1, -1)
}
// </vc-code>

}
fn main() {}