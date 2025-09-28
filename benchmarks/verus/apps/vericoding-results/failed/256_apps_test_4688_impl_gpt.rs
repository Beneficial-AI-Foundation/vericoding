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
/* helper modified by LLM (iteration 2): prove nonnegativity of power for base >= 0 and exp >= 0 */
proof fn lemma_power_nonneg(base: int, exp: int)
    requires
        base >= 0,
        exp >= 0,
    ensures
        power(base, exp) >= 0,
    decreases exp
{
    if exp <= 0 {
        assert(power(base, exp) == 1);
    } else {
        lemma_power_nonneg(base, exp - 1);
        assert(power(base, exp) == base * power(base, exp - 1));
        assert(base >= 0);
        assert(power(base, exp - 1) >= 0);
        assert(base * power(base, exp - 1) >= 0);
    }
}

/* helper modified by LLM (iteration 2): prove power(base, exp) >= 1 for base >= 1 and nat exp */
proof fn lemma_power_ge_one(base: int, exp: nat)
    requires
        base >= 1,
    ensures
        power(base, exp as int) >= 1,
    decreases exp
{
    if exp == 0 {
        assert(power(base, 0) == 1);
    } else {
        lemma_power_ge_one(base, exp - 1);
        assert(power(base, exp as int) == base * power(base, (exp - 1) as int));
        assert(base >= 1);
        assert(power(base, (exp - 1) as int) >= 1);
        assert(base * power(base, (exp - 1) as int) >= 1);
    }
}

/* helper modified by LLM (iteration 2): show painting_ways is strictly positive for valid inputs */
proof fn painting_positive(n: int, k: int)
    requires
        valid_input(n, k),
    ensures
        painting_ways(n, k) > 0,
{
    assert(k >= 2);
    assert(n >= 1);
    if n == 1 {
        assert(power(k - 1, 0) == 1);
        assert(painting_ways(n, k) == k * 1);
        assert(k * 1 > 0);
    } else {
        let exp: nat = (n - 1) as nat;
        assert(k - 1 >= 1);
        lemma_power_ge_one(k - 1, exp);
        assert(power(k - 1, n - 1) >= 1);
        assert(k >= 2);
        assert(k * power(k - 1, n - 1) >= 2);
        assert(k * power(k - 1, n - 1) > 0);
    }
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
    /* code modified by LLM (iteration 2): compute using i8 arithmetic only; proofs kept in ghost code */
    let mut r: i8 = 1;
    let base: i8 = k - 1;
    let mut e: i8 = if n <= 1 { 0 } else { n - 1 };
    while e > 0 {
        r = r * base;
        e = e - 1;
    }
    let res: i8 = k * r;
    proof { painting_positive(n as int, k as int); }
    res
}
// </vc-code>


}

fn main() {}