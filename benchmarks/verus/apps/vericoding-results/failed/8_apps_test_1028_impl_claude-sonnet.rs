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
/* helper modified by LLM (iteration 5): moved lemma calls inside proof blocks */
proof fn lemma_div_mod_properties(n: int, m: int)
    requires n >= 0, m > 0
    ensures
        n == (n / m) * m + (n % m),
        0 <= n % m < m
{
    assert(n == (n / m) * m + (n % m)) by(nonlinear_arith);
    assert(0 <= n % m < m) by(nonlinear_arith);
}

proof fn lemma_comb2_monotonic(a: int, b: int)
    requires a >= 0, b >= a
    ensures comb2(a) <= comb2(b)
{
    assert(a * (a - 1) / 2 <= b * (b - 1) / 2) by(nonlinear_arith);
}

proof fn lemma_min_max_relationship(n: int, m: int)
    requires valid_input(n, m)
    ensures min_friendship_pairs(n, m) <= max_friendship_pairs(n, m)
{
    let k = n / m;
    let p = n % m;
    lemma_comb2_monotonic(k, n - m + 1);
    lemma_comb2_monotonic(k + 1, n - m + 1);
    assert(min_friendship_pairs(n, m) <= max_friendship_pairs(n, m)) by(nonlinear_arith);
}

fn compute_comb2(x: i8) -> (result: i8)
    requires x >= 0, x <= 12
    ensures result == comb2(x as int)
{
    assert(x * (x - 1) / 2 == comb2(x as int)) by(nonlinear_arith);
    assert(x * (x - 1) <= 132) by(nonlinear_arith);
    x * (x - 1) / 2
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
    /* code modified by LLM (iteration 5): wrapped lemma calls in proof blocks */
    let k = n / m;
    let p = n % m;
    
    proof {
        lemma_div_mod_properties(n as int, m as int);
    }
    assert(0 <= k <= 12);
    assert(0 <= k + 1 <= 12);
    assert(k + 1 >= 0);
    
    let min_val = p * compute_comb2(k + 1) + (m - p) * compute_comb2(k);
    let max_val = compute_comb2(n - m + 1);
    
    proof {
        lemma_min_max_relationship(n as int, m as int);
    }
    
    (min_val, max_val)
}
// </vc-code>


}

fn main() {}