// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn power(base: int, exp: int) -> int
  decreases exp when exp >= 0
{
  if exp <= 0 { 1 } else { base * power(base, exp - 1) }
}

spec fn valid_input(n: int, k: int) -> bool
{
  1 <= n <= 1000 && 2 <= k <= 1000
}

spec fn painting_ways(n: int, k: int) -> int
{
  if valid_input(n, k) { k * power(k - 1, n - 1) } else { 0 }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): prove power(base, exp) >= 1 for base >= 1 and exp >= 0 */
proof fn power_positive(base: int, exp: int)
    requires
        base >= 1,
        exp >= 0,
    ensures
        power(base, exp) >= 1,
    decreases
        exp
{
    if exp == 0 {
        assert(power(base, 0) == 1);
    } else {
        power_positive(base, exp - 1);
        assert(power(base, exp - 1) >= 1);
        assert(power(base, exp) == base * power(base, exp - 1));
        assert(power(base, exp) >= 1);
    }
}

/* helper modified by LLM (iteration 5): prove painting_ways(n,k) > 0 when valid_input(n,k) */
proof fn painting_ways_positive(n: int, k: int)
    requires
        valid_input(n, k),
    ensures
        painting_ways(n, k) > 0,
{
    let base = k - 1;
    let exp = n - 1;
    assert(1 <= n);
    assert(2 <= k);
    assert(base >= 1);
    assert(exp >= 0);
    power_positive(base, exp);
    assert(painting_ways(n, k) == k * power(base, exp));
    assert(power(base, exp) >= 1);
    assert(k * power(base, exp) > 0);
}

// </vc-helpers>

// <vc-spec>
fn solve(n: i8, k: i8) -> (result: i8)
  requires 
    valid_input(n as int, k as int)
  ensures 
    result as int == painting_ways(n as int, k as int),
    result > 0
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): compute painting_ways via iterative exponentiation and call proof in a proof block */
  let base_i: i128 = (k as i128) - 1;
  let exp_i: i128 = (n as i128) - 1;
  let mut acc: i128 = 1;
  let mut i: i128 = 0;
  while i < exp_i
      invariant
          0 <= i && i <= exp_i,
          acc as int == power((k as int - 1), i as int),
      decreases
          exp_i - i
  {
      acc = acc * base_i;
      i = i + 1;
  }
  let ways_i: i128 = (k as i128) * acc;
  let result: i8 = ways_i as i8;
  assert(i == exp_i);
  assert(acc as int == power((k as int - 1), i as int));
  assert(acc as int == power((k as int - 1), (n as int - 1)));
  assert(painting_ways(n as int, k as int) == k as int * power((k as int - 1), (n as int - 1)));
  assert((ways_i as int) == k as int * acc as int);
  assert((ways_i as int) == painting_ways(n as int, k as int));
  proof {
      painting_ways_positive(n as int, k as int);
  }
  assert(result as int == painting_ways(n as int, k as int));
  assert(result > 0);
  result
}

// </vc-code>


}

fn main() {}