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
proof fn power_positive(base: int, exp: int)
    requires
        base > 0,
        exp >= 0,
    ensures
        power(base, exp) > 0,
    decreases exp
{
    /* helper modified by LLM (iteration 5): fixed base case for exp == 0 */
    if exp == 0 {
        assert(power(base, exp) == 1);
    } else {
        power_positive(base, exp - 1);
        assert(power(base, exp) == base * power(base, exp - 1));
        assert(power(base, exp - 1) > 0);
        assert(base > 0);
        assert(power(base, exp) > 0);
    }
}

proof fn power_computation(base: int, exp: int)
    requires
        exp >= 0,
    ensures
        power(base, exp) == if exp == 0 { 1 } else { base * power(base, exp - 1) },
{
}

fn compute_power(base: i8, exp: i8) -> (result: i8)
    requires
        base >= 0,
        exp >= 0,
        exp <= 6,
        base <= 100,
        base > 0,
        power(base as int, exp as int) <= 127,
    ensures
        result as int == power(base as int, exp as int),
        result > 0,
{
    proof {
        power_positive(base as int, exp as int);
        assert(power(base as int, exp as int) > 0);
    }
    
    if exp == 0 {
        1
    } else {
        let mut result = 1i8;
        let mut i = 0i8;
        while i < exp
            invariant
                0 <= i <= exp,
                result as int == power(base as int, i as int),
                result > 0,
                base > 0,
                result <= 127,
                base <= 100,
            decreases exp - i
        {
            proof {
                power_positive(base as int, i as int);
                power_positive(base as int, (i + 1) as int);
                assert(power(base as int, (i + 1) as int) == base as int * power(base as int, i as int));
                assert(result as int * base as int <= 127);
            }
            i = i + 1;
            result = result * base;
        }
        result
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
    /* code modified by LLM (iteration 5): added stronger bounds checking and overflow prevention */
    let first_post = k;
    let remaining_posts = n - 1;
    let choices_per_remaining = k - 1;
    
    proof {
        assert(k >= 2);
        assert(n >= 1);
        assert(choices_per_remaining >= 1);
        assert(remaining_posts >= 0);
        assert(remaining_posts <= 999);
        assert(choices_per_remaining <= 999);
        assert(remaining_posts <= 6);
        assert(choices_per_remaining <= 100);
        power_positive((k - 1) as int, (n - 1) as int);
        assert(power((k - 1) as int, (n - 1) as int) <= 127);
    }
    
    let ways_for_remaining = compute_power(choices_per_remaining, remaining_posts);
    
    proof {
        assert(first_post <= 127);
        assert(ways_for_remaining <= 127);
        assert(first_post as int * ways_for_remaining as int <= 127 * 127);
        assert(first_post as int * ways_for_remaining as int <= 16129);
        assert(first_post as int * ways_for_remaining as int <= 127);
    }
    
    let total_ways = first_post * ways_for_remaining;
    
    proof {
        assert(total_ways > 0);
        assert(total_ways as int == k as int * power((k - 1) as int, (n - 1) as int));
        assert(total_ways as int == painting_ways(n as int, k as int));
    }
    
    total_ways
}
// </vc-code>


}

fn main() {}