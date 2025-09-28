use vstd::prelude::*;

verus! {

// <vc-helpers>
// Helper function to prove that if we're at position (i, j) and a[i][j] < key,
// then all elements to the left of j in row i are also < key
proof fn lemma_row_elements_less_than_key(a: &Vec<Vec<i32>>, i: int, j: int, key: i32)
    requires
        0 <= i < a.len(),
        0 <= j < a@[i].len(),
        a@[i]@[j] < key,
        forall|i: int, j: int, j_prime: int| 
            0 <= i < a.len() && 0 <= j < a@[i].len() && 0 <= j_prime < a@[i].len() && j < j_prime
            ==> a@[i]@[j] <= a@[i]@[j_prime],
    ensures
        forall|j_prime: int| 0 <= j_prime <= j && j_prime < a@[i].len() ==> a@[i]@[j_prime] < key
{
    assert forall|j_prime: int| 0 <= j_prime <= j && j_prime < a@[i].len() implies a@[i]@[j_prime] < key by {
        if j_prime < j {
            assert(0 <= j_prime < a@[i].len());
            assert(0 <= j < a@[i].len());
            assert(a@[i]@[j_prime] <= a@[i]@[j]);
            assert(a@[i]@[j] < key);
        } else {
            assert(j_prime == j);
            assert(a@[i]@[j] < key);
        }
    }
}

// Helper function to prove that if we're at position (i, j) and a[i][j] > key,
// then all elements below i in column j are also > key
proof fn lemma_column_elements_greater_than_key(a: &Vec<Vec<i32>>, i: int, j: int, key: i32)
    requires
        0 <= i < a.len(),
        0 <= j < a@[0].len(),
        a@[i]@[j] > key,
        forall|i: int| 0 <= i < a.len() ==> a@[i].len() == a@[0].len(),
        forall|i: int, i_prime: int, j: int| 
            0 <= i < a.len() && 0 <= i_prime < a.len() && 0 <= j < a@[0].len() && i < i_prime
            ==> a@[i]@[j] <= a@[i_prime]@[j],
    ensures
        forall|i_prime: int| i <= i_prime < a.len() ==> a@[i_prime]@[j] > key
{
    assert forall|i_prime: int| i <= i_prime < a.len() implies a@[i_prime]@[j] > key by {
        if i < i_prime {
            assert(0 <= j < a@[0].len());
            assert(a@[i]@[j] <= a@[i_prime]@[j]);
            assert(a@[i]@[j] > key);
        } else {
            assert(i == i_prime);
            assert(a@[i]@[j] > key);
        }
    }
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
    let m = a.len();
    let n = a[0].len();
    
    // Start from top-right corner
    let mut row: usize = 0;
    let mut col: usize = n - 1;
    
    loop
        invariant
            row <= m,
            col < n,
            forall|i: int| 0 <= i < a.len() ==> a@[i].len() == a@[0].len(),
            // Each row is sorted
            forall|i: int, j: int, j_prime: int| 
                0 <= i < a.len() && 0 <= j < a@[i].len() && 0 <= j_prime < a@[i].len() && j < j_prime
                ==> a@[i]@[j] <= a@[i]@[j_prime],
            // Each column is sorted
            forall|i: int, i_prime: int, j: int| 
                0 <= i < a.len() && 0 <= i_prime < a.len() && 0 <= j < a@[0].len() && i < i_prime
                ==> a@[i]@[j] <= a@[i_prime]@[j],
            // Key exists in the remaining search space
            exists|i: int, j: int| 
                row <= i < m && 0 <= j <= col && j < n
                && a@[i]@[j] == key,
            // All elements above row in columns > col are > key
            forall|i: int, j: int|
                0 <= i < row && col < j < n
                ==> a@[i]@[j] > key,
            // All elements to the right of col in rows < row are > key
            forall|i: int, j: int|
                0 <= i < row && col < j < n
                ==> a@[i]@[j] > key,
        decreases (m - row) + col
    {
        if row >= m {
            // This should not happen due to invariant
            assert(exists|i: int, j: int| row <= i < m && 0 <= j <= col && j < n && a@[i]@[j] == key);
            assert(row <= m);
            assert(false);
            return (0, 0);
        }
        
        assert(row < m);
        assert(col < n);
        assert(a@[row as int].len() == a@[0].len());
        assert(col < a@[row as int].len());
        
        let current = a[row][col];
        
        if current == key {
            return (row, col);
        } else if current < key {
            // Move down - eliminate this row
            proof {
                lemma_row_elements_less_than_key(a, row as int, col as int, key);
                // Prove that key still exists in remaining search space
                let ghost_pair = choose|p: (int, int)| row <= p.0 < m && 0 <= p.1 <= col && p.1 < n && a@[p.0]@[p.1] == key;
                assert(row <= ghost_pair.0 < m && 0 <= ghost_pair.1 <= col && ghost_pair.1 < n && a@[ghost_pair.0]@[ghost_pair.1] == key);
                if ghost_pair.0 == row {
                    // Key was in current row
                    assert(0 <= ghost_pair.1 <= col);
                    assert(ghost_pair.1 < a@[row as int].len());
                    assert(a@[row as int]@[ghost_pair.1] == key);
                    assert(a@[row as int]@[ghost_pair.1] < key);  // From lemma
                    assert(false);
                }
                assert(row + 1 <= ghost_pair.0);
                assert(exists|i: int, j: int| row + 1 <= i < m && 0 <= j <= col && j < n && a@[i]@[j] == key);
            }
            row = row + 1;
        } else {
            // current > key
            // Move left - eliminate this column
            proof {
                lemma_column_elements_greater_than_key(a, row as int, col as int, key);
                // Prove that key still exists in remaining search space
                let ghost_pair = choose|p: (int, int)| row <= p.0 < m && 0 <= p.1 <= col && p.1 < n && a@[p.0]@[p.1] == key;
                assert(row <= ghost_pair.0 < m && 0 <= ghost_pair.1 <= col && ghost_pair.1 < n && a@[ghost_pair.0]@[ghost_pair.1] == key);
                if ghost_pair.1 == col {
                    // Key was in current column
                    assert(row <= ghost_pair.0 < m);
                    assert(a@[ghost_pair.0]@[col as int] == key);
                    assert(a@[ghost_pair.0]@[col as int] > key);  // From lemma
                    assert(false);
                }
                assert(ghost_pair.1 < col);
                if col > 0 {
                    assert(exists|i: int, j: int| row <= i < m && 0 <= j <= col - 1 && j < n && a@[i]@[j] == key);
                }
            }
            
            if col == 0 {
                // This should not happen due to invariant
                assert(exists|i: int, j: int| row <= i < m && 0 <= j <= col && j < n && a@[i]@[j] == key);
                assert(exists|i: int, j: int| row <= i < m && 0 <= j <= 0 && j < n && a@[i]@[j] == key);
                assert(exists|i: int, j: int| row <= i < m && j == 0 && a@[i]@[j] == key);
                assert(exists|i: int| row <= i < m && a@[i]@[0] == key);
                let ghost_i = choose|i: int| row <= i < m && a@[i]@[0] == key;
                assert(row <= ghost_i < m && a@[ghost_i]@[0] == key);
                assert(a@[ghost_i]@[0] > key);  // From lemma
                assert(false);
                return (0, 0);
            }
            col = col - 1;
        }
    }
}
// </vc-code>

fn main() {
}

}