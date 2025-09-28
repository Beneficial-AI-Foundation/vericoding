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
fn comb2_impl(n: int) -> int
  requires n >= 0
  ensures result == comb2(n)
{
  n * (n - 1) / 2
}

fn min_friendship_pairs_impl(n: int, m: int) -> int
  requires valid_input(n, m)
  ensures result == min_friendship_pairs(n, m)
{
  let k = n / m;
  let p = n % m;
  p * comb2_impl(k + 1) + (m - p) * comb2_impl(k)
}

fn max_friendship_pairs_impl(n: int, m: int) -> int
  requires valid_input(n, m)
  ensures result == max_friendship_pairs(n, m)
{
  comb2_impl(n - m + 1)
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
    /* code modified by LLM (iteration 3): Fix int type usage in executable code */
    let min_pairs = min_friendship_pairs_impl(n as int, m as int);
    let max_pairs = max_friendship_pairs_impl(n as int, m as int);
    (min_pairs as i8, max_pairs as i8)
}
// </vc-code>


}

fn main() {}