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
/* helper modified by LLM (iteration 5): [add upper bound on n to prevent overflow and prove relation to spec] */
fn exec_comb2(n: i64) -> (r: i64)
    requires
        0 <= n,
        n < 2_000_000_000, // this bound is large enough for the callsites and prevents overflow
    ensures r == comb2(n as int)
{
    proof {
        // prove that exec arithmetic corresponds to spec arithmetic
        vstd::arithmetic::mul_is_mul_int(n, n - 1);
        vstd::arithmetic::div_is_div_int(n * (n - 1), 2);
    }
    n * (n - 1) / 2
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
    /* code modified by LLM (iteration 5): [added assertions to prove bounds and guide verifier] */
    let n_64 = n as i64;
    let m_64 = m as i64;

    assert(1 <= m_64 <= n_64 <= 127) by {
        assert(1 <= m as int <= n as int) because {
            valid_input(n as int, m as int);
        }
    };

    let k = n_64 / m_64;
    let p = n_64 % m_64;

    assert(k + 1 <= n_64 + 1 <= 128);
    assert(n_64 - m_64 + 1 <= n_64);

    let min_pairs = p * exec_comb2(k + 1) + (m_64 - p) * exec_comb2(k);
    let max_pairs = exec_comb2(n_64 - m_64 + 1);

    proof {
        vstd::arithmetic::div_is_div_int(n_64, m_64);
        vstd::arithmetic::mod_is_mod_int(n_64, m_64);
        assert(k as int == (n as int) / (m as int));
        assert(p as int == (n as int) % (m as int));
        assert(min_pairs as int == min_friendship_pairs(n as int, m as int));
        assert(max_pairs as int == max_friendship_pairs(n as int, m as int));
    }

    (min_pairs as i8, max_pairs as i8)
}
// </vc-code>


}

fn main() {}