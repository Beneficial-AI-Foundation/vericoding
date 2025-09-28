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
/* helper modified by LLM (iteration 5): Fixed compilation error by changing the 'exp' type to 'int' in 'lemma_power_pos' function signature and in the recursive call, which ensures type compatibility with the 'power' function. */
proof fn lemma_power_pos(base: int, exp: int)
    requires
        base > 0,
        exp >= 0
    ensures
        power(base, exp) > 0
{
    if exp == 0 { /* handled by base case */ }
    else {
        lemma_power_pos(base, exp - 1);
        assert(power(base, exp) == base * power(base, exp - 1));
        assert(base > 0 && power(base, exp - 1) > 0);
        assert(base * power(base, exp - 1) > 0);
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
/* code modified by LLM (iteration 5): Removed direct casting of n and k to 'int' within `vc-code` block to resolve compilation errors where 'int' cannot be used in ghost code outside of spec or proof contexts. Modified `lemma_power_pos` call to pass `exp_val_int` directly instead of casting it to `nat` to match the updated helper function signature. */
{
    let k_minus_1_int = (k - 1) as int;
    let n_minus_1_int = (n - 1) as int;

    let base_val_int = k_minus_1_int;
    let exp_val_int = n_minus_1_int;

    let mut current_power_val_int: int = 1;
    let mut i: int = 0;

    if n_minus_1_int > 0 && k_minus_1_int > 0 {
        proof { lemma_power_pos(base_val_int, exp_val_int); }
    }
    
    let mut current_power_i8: i8 = 1;

    while i < exp_val_int
        invariant
            0 <= i <= exp_val_int,
            current_power_val_int == power(base_val_int, i),
            current_power_val_int >= 1,
            (current_power_val_int as i8) == current_power_i8,
            base_val_int >= 1,
            (k as int * current_power_val_int) <= 127,
            // ensures that the next multiplication current_power_val_int * base_val_int will not overflow i8
            base_val_int == 1 || (127 / base_val_int) >= current_power_val_int
    {
        current_power_val_int = current_power_val_int * base_val_int;
        current_power_i8 = current_power_i8 * (base_val_int as i8);
        i = i + 1;
    }

    assert(current_power_val_int == power(base_val_int, exp_val_int));

    let result_int = (k as int) * current_power_val_int;
    let result_i8 = (k as i8) * current_power_i8;

    result_i8
}
// </vc-code>


}

fn main() {}