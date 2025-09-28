use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn lemma_key_exists_witness(a: &Vec<Vec<i32>>, key: i32) -> (result: (usize, usize))
    requires 
        a.len() > 0,
        forall|i: int| 0 <= i < a.len() ==> #[trigger] a@[i].len() == a@[0].len(),
        a@[0].len() > 0,
        exists|i: int, j: int| 
            0 <= i < a.len() && 0 <= j < a@[0].len()
            && #[trigger] a@[i]@[j] == key
    ensures
        result.0 < a.len(),
        result.1 < a@[0].len(),
        a@[result.0 as int]@[result.1 as int] == key
{
    let witness_i = choose|i: int| exists|j: int| 0 <= i < a.len() && 0 <= j < a@[0].len() && a@[i]@[j] == key;
    let witness_j = choose|j: int| 0 <= witness_i < a.len() && 0 <= j < a@[0].len() && a@[witness_i]@[j] == key;
    (witness_i as usize, witness_j as usize)
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
    let mut row = 0usize;
    let mut col = a[0].len() - 1;
    
    loop 
        invariant
            row < a.len(),
            col < a@[0].len(),
            // Key must be in the remaining search space
            forall|i: int, j: int| 
                0 <= i < a.len() && 0 <= j < a@[0].len() && a@[i]@[j] == key
                ==> (i >= row || j >= col),
    {
        let current = a@[row as int]@[col as int];
        
        if current == key {
            return (row, col);
        } else if current > key {
            if col == 0 {
                // This shouldn't happen given our preconditions
                proof {
                    let witness = lemma_key_exists_witness(a, key);
                    assert(a@[witness.0 as int]@[witness.1 as int] == key);
                    assert(witness.0 >= row || witness.1 >= col);
                    if witness.0 >= row {
                        assert(a@[row as int]@[col as int] <= a@[witness.0 as int]@[col as int]);
                        assert(a@[witness.0 as int]@[col as int] <= a@[witness.0 as int]@[witness.1 as int]);
                        assert(current <= key);
                        assert(false);
                    } else {
                        assert(witness.1 >= col);
                        assert(witness.1 == col);
                        assert(a@[witness.0 as int]@[witness.1 as int] <= a@[row as int]@[witness.1 as int]);
                        assert(key <= current);
                        assert(false);
                    }
                }
                return (0, 0);
            }
            col = col - 1;
        } else {
            row = row + 1;
            if row >= a.len() {
                // This shouldn't happen given our preconditions
                proof {
                    let witness = lemma_key_exists_witness(a, key);
                    assert(a@[witness.0 as int]@[witness.1 as int] == key);
                    assert(witness.0 >= row || witness.1 >= col);
                    assert(witness.1 >= col);
                    assert(a@[witness.0 as int]@[witness.1 as int] >= a@[witness.0 as int]@[col as int]);
                    assert(a@[witness.0 as int]@[col as int] >= a@[row as int - 1]@[col as int]);
                    assert(key >= current);
                    assert(false);
                }
                return (0, 0);
            }
        }
    }
}
// </vc-code>

fn main() {
}

}