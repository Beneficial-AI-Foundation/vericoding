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
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}