use vstd::prelude::*;

verus! {

// <vc-helpers>
// Empty helpers section
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
    let rows = a.len();
    let cols = a@[0].len();
    let mut i: int = 0;
    let mut j: int = cols as int - 1;
    while i < rows as int && j >= 0
        invariant
            0 <= i < rows as int,
            -1 <= j < cols as int,
            exists|x: int, y: int| 
                i <= x < a.len() && ((x == i && 0 <= y <= j && y < cols as int) || (i < x < a.len() && 0 <= y < cols as int)) && #[trigger] a@[x]@[y] == key
    {
        proof {
            assert(i >= 0 && j >= 0 && i < rows as int && j < cols as int);
            assert(a@[i]@[j] == a[i as usize][j as usize]);
        }
        let val = a[i as usize][j as usize];
        if val == key {
            return (i as usize, j as usize);
        } else if val > key {
            proof {
                // Proof that moving left preserves the invariant
                assert(a@[i]@[j] > key);
                // Since row is sorted, any occurrence of key in this row must be to the left if it exists
            }
            j -= 1;
        } else {
            i += 1;
        }
    }
    assert(false);
    (0, 0)
}
// </vc-code>

fn main() {
}

}