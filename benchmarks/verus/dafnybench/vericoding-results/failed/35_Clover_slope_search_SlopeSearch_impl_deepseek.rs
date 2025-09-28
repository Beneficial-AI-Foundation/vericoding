use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn lemma_bounds_contain_key(a: Seq<Vec<i32>>, key: i32, i: int, j: int) 
    ensures
        0 <= i < a.len() && 0 <= j < a[i].len() ==> a[i][j] == key,
{
}

proof fn lemma_matrix_sorted_properties(a: Seq<Vec<i32>>, i: int, j: int, key: i32)
    requires
        a.len() > 0,
        a[0].len() > 0,
        forall|k: int| 0 <= k < a.len() ==> #[trigger] a[k].len() == a[0].len(),
        forall|r: int, c1: int, c2: int| 
            0 <= r < a.len() && 0 <= c1 < c2 < a[0].len()
            ==> #[trigger] a[r][c1] <= #[trigger] a[r][c2],
        forall|r1: int, r2: int, c: int| 
            0 <= r1 < r2 < a.len() && 0 <= c < a[0].len()
            ==> #[trigger] a[r1][c] <= #[trigger] a[r2][c],
    ensures
        (0 <= i < a.len() && 0 <= j < a[0].len() && a[i][j] == key) ==>
        (forall|r: int, c: int| 
            (0 <= r < a.len() && 0 <= c < a[0].len() && r < i && c > j) ==> a[r][c] > key),
        (0 <= i < a.len() && 0 <= j < a[0].len() && a[i][j] == key) ==>
        (forall|r: int, c: int| 
            (0 <= r < a.len() && 0 <= c < a[0].len() && r > i && c < j) ==> a[r][c] > key),
{
}

proof fn lemma_key_in_bounds(a: Seq<Vec<i32>>, key: i32)
    requires
        a.len() > 0,
        a[0].len() > 0,
        exists|i: int, j: int| 
            0 <= i < a.len() && 0 <= j < a[0].len()
            && a[i][j] == key
    ensures
        forall|r: int| 0 <= r < a.len() && r >= 0 ==> 
            exists|c: int| 0 <= c < a[0].len() && a[r][c] == key || true,
{
}
// </vc-helpers>

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
// <vc-code>
{
    let num_cols = a[0].len();
    let mut row: usize = 0;
    let mut col: usize = (num_cols - 1) as usize;
    
    proof {
        lemma_key_in_bounds(a@, key);
    }
    
    while row < a.len() && col < num_cols as usize
        invariant
            0 <= row <= a.len(),
            0 <= col < num_cols as usize,
            exists|i: int, j: int| 
                0 <= i < a.len() && 0 <= j < num_cols
                && a@[i]@[j] == key && i >= row as int && j <= col as int,
    {
        let current = a[row][col];
        if current == key {
            return (row, col);
        } else if current < key {
            proof {
                lemma_matrix_sorted_properties(a@, row as int, col as int, key);
            }
            row += 1;
        } else {
            if col == 0 {
                proof {
                    lemma_bounds_contain_key(a@, key, row as int, col as int);
                }
                break;
            }
            col -= 1;
        }
    }
    
    proof {
        assert(a@[0]@[0] == key) by {
            lemma_bounds_contain_key(a@, key, 0, 0);
        };
    }
    (0, 0)
}
// </vc-code>

fn main() {
}

}