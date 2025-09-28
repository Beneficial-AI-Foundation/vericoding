// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn slope_search(a: &Vec<Vec<i32>>, key: i32) -> (result: (usize, usize))
  requires 
      a.len() > 0,
      forall|i: int| 0 <= i < a.len() ==> #[trigger] a@[i].len() == a@[0].len(),
      a@[0].len() > 0,

      forall|i: int, j: int, j_prime: int| 
          0 <= i < a.len() && 0 <= j < j_prime < a@[0].len()
          ==> #[trigger] a@[i]@[j] <= #[trigger] a@[i]@[j_prime],

      forall|i: int, i_prime: int, j: int| 
          0 <= i < i_prime < a.len() && 0 <= j < a@[0].len()
          ==> #[trigger] a@[i]@[j] <= #[trigger] a@[i_prime]@[j],

      exists|i: int, j: int| 
          0 <= i < a.len() && 0 <= j < a@[0].len()
          && #[trigger] a@[i]@[j] == key
  ensures
      result.0 < a.len(),
      result.1 < a@[0].len(),
      a@[result.0 as int]@[result.1 as int] == key
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): fixed compilation error in invariant and corrected bound for loop variable i */
{
    let m = a.len();
    let n = a[0].len();

    let mut i: usize = 0;
    let mut j: usize = n - 1;

    let ghost m_int = m as int;
    let ghost n_int = n as int;

    while i < m && j < n
        invariant
            m == a.len(),
            n == a[0].len(),
            forall|row: int| 0 <= row < a.len() ==> #[trigger] a@[row].len() == n,
            0 <= i as int <= m_int,
            0 <= j as int && j as int < n_int,
            forall|row: int, c1: int, c2: int|
                0 <= row < m_int && 0 <= c1 < c2 < n_int
                ==> #[trigger] a@[row]@[c1] <= #[trigger] a@[row]@[c2],
            forall|r1: int, r2: int, col: int|
                0 <= r1 < r2 < m_int && 0 <= col < n_int
                ==> #[trigger] a@[r1]@[col] <= #[trigger] a@[r2]@[col],
            exists|r: int, c: int|
                i as int <= r < m_int && 0 <= c <= j as int && #[trigger] a@[r]@[c] == key
        decreases (m_int - i as int) + (j as int)
    {
        let current = a[i][j];
        if current == key {
            return (i, j);
        } else if current < key {
            proof {
                let (r_k, c_k) = choose |r: int, c: int| i as int <= r < m_int && 0 <= c <= j as int && a@[r]@[c] == key;
                if r_k == i as int {
                    assert(a@[i as int]@[c_k] <= a@[i as int]@[j as int]);
                    assert(key <= current);
                    assert(false);
                }
                assert(r_k > i as int);
                assert(exists|r: int, c: int| (i + 1) as int <= r < m_int && 0 <= c <= j as int && a@[r]@[c] == key);
            }
            i = i + 1;
        } else { // current > key
            proof {
                let (r_k, c_k) = choose |r: int, c: int| i as int <= r < m_int && 0 <= c <= j as int && a@[r]@[c] == key;
                if j == 0 {
                    assert(c_k == 0);
                    assert(a@[i as int]@[0] <= a@[r_k]@[0]);
                    assert(current <= key);
                    assert(false);
                }
                assert(j > 0);

                if c_k == j as int {
                    assert(a@[i as int]@[j as int] <= a@[r_k]@[j as int]);
                    assert(current <= key);
                    assert(false);
                }
                assert(c_k < j as int);
                assert(exists|r: int, c: int| i as int <= r < m_int && 0 <= c <= (j - 1) as int && a@[r]@[c] == key);
            }
            j = j - 1;
        }
    }
    proof {
        assert(false);
    }
    unreachable!();
}
// </vc-code>

}
fn main() {}