use vstd::prelude::*;

verus! {

// <vc-helpers>
fn lemma_key_exists_witness(a: &Vec<Vec<i32>>, key: i32) -> (witness: (usize, usize))
    requires
        a.len() > 0,
        forall|i: int| 0 <= i < a.len() ==> #[trigger] a@[i].len() == a@[0].len(),
        a@[0].len() > 0,
        exists|i: int, j: int| 
            0 <= i < a.len() && 0 <= j < a@[0].len()
            && #[trigger] a@[i]@[j] == key
    ensures
        witness.0 < a.len(),
        witness.1 < a@[0].len(),
        a@[witness.0 as int]@[witness.1 as int] == key
{
    let mut found_i = 0;
    let mut found_j = 0;
    
    for i in 0..a.len()
        invariant
            0 <= i <= a.len(),
            exists|ii: int, jj: int| 
                0 <= ii < a.len() && 0 <= jj < a@[0].len()
                && #[trigger] a@[ii]@[jj] == key
    {
        for j in 0..a@[i as int].len()
            invariant
                0 <= i < a.len(),
                0 <= j <= a@[i as int].len(),
                exists|ii: int, jj: int| 
                    0 <= ii < a.len() && 0 <= jj < a@[0].len()
                    && #[trigger] a@[ii]@[jj] == key
        {
            if a@[i as int]@[j as int] == key {
                found_i = i;
                found_j = j;
                break;
            }
        }
    }
    
    (found_i, found_j)
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
{
    let rows = a.len();
    let cols = a[0].len();
    
    let mut row: usize = 0;
    let mut col: usize = cols - 1;
    
    loop 
        invariant
            0 <= row < rows,
            0 <= col < cols,
            exists|i: int, j: int| 
                row <= i < a.len() && 0 <= j <= col
                && #[trigger] a@[i]@[j] == key,
            forall|i: int, j: int|
                0 <= i < row && col < j < a@[0].len()
                ==> #[trigger] a@[i]@[j] > key,
            forall|i: int, j: int|
                row <= i < a.len() && col < j < a@[0].len()
                ==> #[trigger] a@[i]@[j] > key,
            forall|i: int, j: int|
                row < i < a.len() && 0 <= j < col
                ==> #[trigger] a@[i]@[j] < key,
            forall|i: int, j: int|
                0 <= i < row && 0 <= j < col
                ==> #[trigger] a@[i]@[j] < key
    {
        let current = a[row][col];
        
        if current == key {
            return (row, col);
        } else if current > key {
            if col == 0 {
                proof {
                    assert(false);
                }
            }
            col = col - 1;
        } else {
            row = row + 1;
            if row >= rows {
                proof {
                    assert(false);
                }
            }
        }
    }
}
// </vc-code>

fn main() {
}

}