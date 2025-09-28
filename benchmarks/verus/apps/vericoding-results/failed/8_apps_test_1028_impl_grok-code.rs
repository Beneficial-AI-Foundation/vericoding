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
fn comb2_exec(n: i32) -> (result: i32)
    requires n >= 0
    ensures comb2(n as int) == result as int
{
    /* helper modified by LLM (iteration 2): named return value to enable use of result in postcondition */
    n * (n - 1) / 2
}

fn min_friendship_pairs_exec(n: i32, m: i32) -> (result: i32)
    requires valid_input(n as int, m as int)
    ensures min_friendship_pairs(n as int, m as int) == result as int
{
    /* helper modified by LLM (iteration 2): named return value to enable use of result in postcondition */
    let k = n / m;
    let p = n % m;
    p * comb2_exec(k + 1) + (m - p) * comb2_exec(k)
}

fn max_friendship_pairs_exec(n: i32, m: i32) -> (result: i32)
    requires valid_input(n as int, m as int)
    ensures max_friendship_pairs(n as int, m as int) == result as int
{
    /* helper modified by LLM (iteration 2): named return value to enable use of result in postcondition */
    comb2_exec(n - m + 1)
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
    /* code modified by LLM (iteration 2): implemented calculation of min and max friendship pairs using exec helper functions */
    let min_val = min_friendship_pairs_exec(n as i32, m as i32);
    let max_val = max_friendship_pairs_exec(n as i32, m as i32);
    (min_val as i8, max_val as i8)
}
// </vc-code>


}

fn main() {}