// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn comb2(n: int) -> int
  recommends n >= 0
{
  n * (n - 1) / 2
}

spec fn valid_input(n: int, m: int) -> bool
{
  1 <= m <= n
}

spec fn min_friendship_pairs(n: int, m: int) -> int
  recommends valid_input(n, m)
{
  let k = n / m;
  let p = n % m;
  p * comb2(k + 1) + (m - p) * comb2(k)
}

spec fn max_friendship_pairs(n: int, m: int) -> int
  recommends valid_input(n, m)
{
  comb2(n - m + 1)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): div/mod properties */
fn div_mod_props(n: int, m: int)
    requires m > 0,
    ensures
        n == m * (n / m) + n % m,
        0 <= n % m && n % m < m,
{
    proof {
        assert(n == m * (n / m) + n % m);
        assert(0 <= n % m && n % m < m);
    }
}

/* helper modified by LLM (iteration 3): comb2 nonnegativity */
fn comb2_nonneg(n: int)
    requires n >= 0,
    ensures comb2(n) >= 0,
{
    proof {
        if n <= 1 {
            assert(comb2(n) == 0);
        } else {
            assert(comb2(n) == n * (n - 1) / 2);
            assert(n * (n - 1) >= 0);
            assert(comb2(n) >= 0);
        }
    }
}

// </vc-helpers>

// <vc-spec>
fn solve(n: i8, m: i8) -> (result: (i8, i8))
  requires valid_input(n as int, m as int)
  ensures 
      result.0 >= 0 &&
      result.1 >= 0 &&
      result.0 <= result.1 &&
      result.0 == min_friendship_pairs(n as int, m as int) &&
      result.1 == max_friendship_pairs(n as int, m as int)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): compute using machine integers (i128) and prove equality to spec in a proof block */
  let k = n / m;
  let p = n % m;
  let k128 = k as i128;
  let p128 = p as i128;
  let m128 = m as i128;
  let n128 = n as i128;
  let min_pairs = p128 * ((k128 + 1) * k128 / 2) + (m128 - p128) * (k128 * (k128 - 1) / 2);
  let max_pairs = (n128 - m128 + 1) * (n128 - m128) / 2;
  let min_res = min_pairs as i8;
  let max_res = max_pairs as i8;
  proof {
      let n_int = n as int;
      let m_int = m as int;
      assert(min_pairs as int == min_friendship_pairs(n_int, m_int));
      assert(max_pairs as int == max_friendship_pairs(n_int, m_int));
      assert(min_pairs as int >= 0);
      assert(max_pairs as int >= 0);
  }
  (min_res, max_res)
}

// </vc-code>


}

fn main() {}