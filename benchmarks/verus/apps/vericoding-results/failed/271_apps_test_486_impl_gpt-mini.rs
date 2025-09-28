// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn product_of_digits(x: int) -> int
  recommends x >= 0
  decreases x
{
  if x == 0 { 1 }
  else if x < 10 { x }
  else { (x % 10) * product_of_digits(x / 10) }
}

spec fn max_product_of_digits_in_range(n: int) -> int
  recommends n >= 1
  decreases n
  when n >= 1
{
  if n == 1 { 1 }
  else {
    let current = product_of_digits(n);
    let rest = max_product_of_digits_in_range(n - 1);
    if current > rest { current } else { rest }
  }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): max_le_from_forall - proves max <= m given forall */
proof fn max_le_from_forall(n: int, m: int)
    requires
        n >= 1,
        forall|k: int| 1 <= k && k <= n ==> product_of_digits(k) <= m,
    ensures
        max_product_of_digits_in_range(n) <= m,
    decreases n
{
    if n == 1 {
        assert(max_product_of_digits_in_range(1) == 1);
        assert(product_of_digits(1) <= m);
        assert(max_product_of_digits_in_range(1) <= m);
    } else {
        let current = product_of_digits(n);
        max_le_from_forall(n - 1, m);
        let prev = max_product_of_digits_in_range(n - 1);
        assert(prev <= m);
        assert(current <= m);
        assert(if current > prev { current } else { prev } <= m);
        assert(max_product_of_digits_in_range(n) <= m);
    }
}

/* helper modified by LLM (iteration 5): characterize_max - shows max equals given m when exists witness */
proof fn characterize_max(n: int, m: int)
    requires
        n >= 1,
        forall|k: int| 1 <= k && k <= n ==> product_of_digits(k) <= m,
        exists|k: int| 1 <= k && k <= n && product_of_digits(k) == m,
    ensures
        max_product_of_digits_in_range(n) == m,
    decreases n
{
    if n == 1 {
        assert(max_product_of_digits_in_range(1) == 1);
        assert(m == 1);
    } else {
        let current = product_of_digits(n);
        if current == m {
            max_le_from_forall(n - 1, m);
            let prev = max_product_of_digits_in_range(n - 1);
            assert(prev <= m);
            assert(if current > prev { current } else { prev } == m);
            assert(max_product_of_digits_in_range(n) == m);
        } else {
            let k0 = choose(|k: int| 1 <= k && k <= n && product_of_digits(k) == m);
            assert(1 <= k0 && k0 <= n && product_of_digits(k0) == m);
            assert(product_of_digits(n) != m);
            assert(k0 != n);
            characterize_max(n - 1, m);
            let prev = max_product_of_digits_in_range(n - 1);
            assert(prev == m);
            assert(if current > prev { current } else { prev } == m);
            assert(max_product_of_digits_in_range(n) == m);
        }
    }
}

// </vc-helpers>

// <vc-spec>
fn solve(n: i8) -> (result: i8)
  requires 
    n >= 1
  ensures 
    result as int == max_product_of_digits_in_range(n as int),
    result >= 1,
    forall|k: int| 1 <= k <= n as int ==> product_of_digits(k) <= result as int,
    exists|k: int| 1 <= k <= n as int && product_of_digits(k) == result as int
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): iterative computation using mutable res and loop invariants */
  let N: int = n as int;
  let mut res: int = 1;
  let mut i: int = 1;
  while i <= N
      invariant
          1 <= i && i <= N + 1,
          forall|k: int| 1 <= k && k <= i - 1 ==> product_of_digits(k) <= res,
          (i == 1 ==> res == 1),
          (i > 1 ==> exists|k: int| 1 <= k && k <= i - 1 && product_of_digits(k) == res),
      decreases N + 1 - i
  {
      let p: int = product_of_digits(i);
      if p > res { res = p; }
      i = i + 1;
  }

  ghost {
      let m: int = res;
      proof {
          assert(i == N + 1);
          assert(forall|k: int| 1 <= k && k <= N ==> product_of_digits(k) <= m);
          assert(exists|k: int| 1 <= k && k <= N && product_of_digits(k) == m);
          characterize_max(N, m);
      }
  }

  let result: i8 = res as i8;
  result
}

// </vc-code>


}

fn main() {}