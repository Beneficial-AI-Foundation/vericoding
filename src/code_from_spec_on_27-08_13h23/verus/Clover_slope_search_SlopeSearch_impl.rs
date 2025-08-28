use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn lemma_row_sorted(a: &Vec<Vec<i32>>, row: int, col1: int, col2: int)
    requires
        0 <= row < a.len(),
        0 <= col1 <= col2 < a@[0].len(),
        forall|i: int, j: int, j_prime: int| 
            0 <= i < a.len() && 0 <= j < j_prime < a@[0].len()
            ==> #[trigger] a@[i]@[j] <= #[trigger] a@[i]@[j_prime],
    ensures
        a@[row]@[col1] <= a@[row]@[col2]
{
}

proof fn lemma_col_sorted(a: &Vec<Vec<i32>>, col: int, row1: int, row2: int)
    requires
        0 <= col < a@[0].len(),
        0 <= row1 <= row2 < a.len(),
        forall|i: int, i_prime: int, j: int| 
            0 <= i < i_prime < a.len() && 0 <= j < a@[0].len()
            ==> #[trigger] a@[i]@[j] <= #[trigger] a@[i_prime]@[j],
    ensures
        a@[row1]@[col] <= a@[row2]@[col]
{
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn slope_search(a: &Vec<Vec<i32>>, key: i32) -> (result: (usize, usize))
  requires 
      a.len() > 0,
      forall|i: int| 0 <= i < a.len() ==> #[trigger] a@[i].len() == a@[0].len(),
      a@[0].len() > 0,
      // Each row is sorted (non-decreasing)
      forall|i: int, j: int, j_prime: int| 
          0 <= i < a.len() && 0 <= j < j_prime < a@[0].len()
          ==> #[trigger] a@[i]@[j] <= #[trigger] a@[i]@[j_prime],
      // Each column is sorted (non-decreasing)  
      forall|i: int, i_prime: int, j: int| 
          0 <= i < i_prime < a.len() && 0 <= j < a@[0].len()
          ==> #[trigger] a@[i]@[j] <= #[trigger] a@[i_prime]@[j],
      // Key exists in the matrix
      exists|i: int, j: int| 
          0 <= i < a.len() && 0 <= j < a@[0].len()
          && #[trigger] a@[i]@[j] == key
  ensures
      result.0 < a.len(),
      result.1 < a@[0].len(),
      a@[result.0 as int]@[result.1 as int] == key
// </vc-spec>
// </vc-spec>

// <vc-code>
fn slope_search(a: &Vec<Vec<i32>>, key: i32) -> (result: (usize, usize))
    requires 
        a.len() > 0,
        forall|i: int| 0 <= i < a.len() ==> #[trigger] a@[i].len() == a@[0].len(),
        a@[0].len() > 0,
        // Each row is sorted (non-decreasing)
        forall|i: int, j: int, j_prime: int| 
            0 <= i < a.len() && 0 <= j < j_prime < a@[0].len()
            ==> #[trigger] a@[i]@[j] <= #[trigger] a@[i]@[j_prime],
        // Each column is sorted (non-decreasing)  
        forall|i: int, i_prime: int, j: int| 
            0 <= i < i_prime < a.len() && 0 <= j < a@[0].len()
            ==> #[trigger] a@[i]@[j] <= #[trigger] a@[i_prime]@[j],
        // Key exists in the matrix
        exists|i: int, j: int| 
            0 <= i < a.len() && 0 <= j < a@[0].len()
            && #[trigger] a@[i]@[j] == key
    ensures
        result.0 < a.len(),
        result.1 < a@[0].len(),
        a@[result.0 as int]@[result.1 as int] == key
{
    let mut row: usize = 0;
    let mut col: usize = a@[0].len() - 1;

    while row < a.len() && col < a@[0].len()
        invariant
            row <= a.len(),
            col < a@[0].len(),
            exists|i: int, j: int| 
                0 <= i < a.len() && 0 <= j < a@[0].len() 
                && #[trigger] a@[i]@[j] == key
                && (i >= row as int || j <= col as int)
    {
        if a@[row as int]@[col as int] == key {
            return (row, col);
        } else if a@[row as int]@[col as int] > key {
            if col > 0 {
                col = col - 1;
            } else {
                break;
            }
        } else {
            row = row + 1;
        }
    }

    // If not found in the slope search, fallback to exhaustive search
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            exists|ii: int, jj: int| 
                0 <= ii < a.len() && 0 <= jj < a@[0].len()
                && #[trigger] a@[ii]@[jj] == key
    {
        let mut j: usize = 0;
        while j < a@[0].len()
            invariant
                i < a.len(),
                j <= a@[0].len(),
                exists|ii: int, jj: int| 
                    0 <= ii < a.len() && 0 <= jj < a@[0].len()
                    && #[trigger] a@[ii]@[jj] == key
        {
            if a@[i as int]@[j as int] == key {
                return (i, j);
            }
            j = j + 1;
        }
        i = i + 1;
    }
    // This line should never be reached due to the precondition that key exists
    (0, 0)
}
// </vc-code>

fn main() {
}

}