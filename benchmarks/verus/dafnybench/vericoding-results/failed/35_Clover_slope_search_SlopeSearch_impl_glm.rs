use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn lemma_matrix_search<a>(
    a: Vec<Vec<i32>>,
    key: i32,
    i0: int,
    j0: int,
    i1: int,
    j1: int,
)
    requires
        0 <= i0 <= i1 < a.len(),
        0 <= j0 <= j1 < a@[0].len(),
        forall|i: int| 0 <= i < a.len() ==> #[trigger] a@[i].len() == a@[0].len(),
        forall|i: int, j: int, j_prime: int|
            0 <= i < a.len() && 0 <= j < j_prime < a@[0].len()
            ==> #[trigger] a@[i]@[j] <= #[trigger] a@[i]@[j_prime],
        forall|i: int, i_prime: int, j: int|
            0 <= i < i_prime < a.len() && 0 <= j < a@[0].len()
            ==> #[trigger] a@[i]@[j] <= #[trigger] a@[i_prime]@[j],
        a@[i0]@[j0] <= key,
        key <= a@[i1]@[j1],
    ensures
        exists|i: int, j: int|
            i0 <= i <= i1 && j0 <= j <= j1 && a@[i]@[j] == key
{
    if i0 == i1 && j0 == j1 {
        assert(a@[i0]@[j0] == key);
    } else if i0 < i1 {
        let mid = i0 + (i1 - i0) / 2;
        if a@[mid]@[j1] >= key {
            lemma_matrix_search(a, key, i0, j0, mid, j1);
        } else {
            lemma_matrix_search(a, key, mid + 1, j0, i1, j1);
        }
    } else {
        assert(j0 < j1);
        let mid = j0 + (j1 - j0) / 2;
        if a@[i1]@[mid] >= key {
            lemma_matrix_search(a, key, i0, j0, i1, mid);
        } else {
            lemma_matrix_search(a, key, i0, mid + 1, i1, j1);
        }
    }
}

proof fn lemma_loop_invariant<a>(
    a: Vec<Vec<i32>>,
    key: i32,
    row: int,
    col: int,
)
    requires
        0 <= row <= a.len(),
        0 <= col < a@[0].len(),
        forall|i: int| 0 <= i < a.len() ==> #[trigger] a@[i].len() == a@[0].len(),
        forall|i: int, j: int, j_prime: int|
            0 <= i < a.len() && 0 <= j < j_prime < a@[0].len()
            ==> #[trigger] a@[i]@[j] <= #[trigger] a@[i]@[j_prime],
        forall|i: int, i_prime: int, j: int|
            0 <= i < i_prime < a.len() && 0 <= j < a@[0].len()
            ==> #[trigger] a@[i]@[j] <= #[trigger] a@[i_prime]@[j],
        exists|i: int, j: int|
            0 <= i < a.len() && 0 <= j < a@[0].len() && a@[i]@[j] == key,
    ensures
        exists|i: int, j: int|
            row <= i < a.len() && 0 <= j <= col && a@[i]@[j] == key
{
    if row == 0 && col == (a@[0].len() - 1) {
        lemma_matrix_search(a, key, 0, 0, (a.len() - 1), (a@[0].len() - 1));
    }
    
    if row > 0 {
        lemma_loop_invariant(a, key, row - 1, col);
    }
    
    if col < (a@[0].len() - 1) {
        lemma_loop_invariant(a, key, row, col + 1);
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
    let mut row = 0;
    let mut col = a[@0].len() - 1;
    
    proof {
        lemma_loop_invariant(*a, key, 0, col as int);
    }
    
    while row < a.len() && col < a[@0].len()
        invariant
            0 <= row <= a.len(),
            0 <= col < a[@0].len(),
            exists|i: int, j: int|
                row <= i < a.len() && 0 <= j <= col && a[@i][@j] == key
    {
        if a[@row][@col] == key {
            return (row, col);
        } else if a[@row][@col] < key {
            row = row + 1;
            proof {
                lemma_loop_invariant(*a, key, row as int, col as int);
            }
        } else {
            assert(col > 0);
            col = col - 1;
            proof {
                lemma_loop_invariant(*a, key, row as int, col as int);
            }
        }
    }
    
    assert(false);
    (0, 0)
}
// </vc-code>

fn main() {
}

}