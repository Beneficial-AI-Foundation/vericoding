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
proof fn convert_range(x: int)
    requires
        x >= 0
    ensures
        x >= 0
{
}

proof fn power_lemma1(base: int, exp: int)
    requires
        base >= 0,
        exp >= 0
    ensures
        power(base, exp + 1) == base * power(base, exp)
    decreases exp
{
    if exp > 0 {
        power_lemma1(base, exp - 1);
    }
}

proof fn power_pos(base: int, exp: int)
    requires
        base >= 0,
        exp >= 0
    ensures
        power(base, exp) >= 0
    decreases exp
{
    if exp > 0 {
        power_pos(base, exp - 1);
    }
}

proof fn power_lemma_zero(base: int)
    requires
        base >= 0
    ensures
        power(base, 0) == 1
{
}

proof fn power_lemma_nonnegative(base: int, exp: int)
    requires
        base >= 0,
        exp >= 0
    ensures
        power(base, exp) >= 0
{
    power_pos(base, exp);
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
    /* code modified by LLM (iteration 5): Fix type conversion issues in recursive calls */
    let mut ways: i16 = k as i16;
    let mut remaining: i8 = n - 1;
    let base: i8 = k - 1;
    
    proof {
        let n_int = n as int;
        let k_int = k as int;
        assert(painting_ways(n_int, k_int) == k_int * power(k_int - 1, n_int - 1)) by {
            assert(valid_input(n_int, k_int));
        };
        power_pos(k_int - 1, n_int - 1);
        convert_range((n - 1) as int);
        convert_range((k - 1) as int);
    }
    
    while remaining > 0
        invariant
            ways as int == (k as int) * power(base as int, remaining as int),
            0 <= remaining <= (n as int) - 1,
            base as int == (k as int) - 1,
            ways > 0
        decreases remaining
    {
        proof {
            power_lemma1(base as int, (remaining as int - 1));
            convert_range((remaining - 1) as int);
        }
        
        ways = ways * base as i16;
        remaining = remaining - 1;
    }
    
    proof {
        power_lemma_zero(base as int);
    }
    
    let result: i8 = ways as i8;
    result
}
// </vc-code>


}

fn main() {}