// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(n: int, a: int, b: int, c: int, d: int, e: int) -> bool {
    n >= 1 && a >= 1 && b >= 1 && c >= 1 && d >= 1 && e >= 1
}

spec fn min_capacity(a: int, b: int, c: int, d: int, e: int) -> int
    recommends a >= 1 && b >= 1 && c >= 1 && d >= 1 && e >= 1
{
    let temp1 = if a <= b { a } else { b };
    let temp2 = if temp1 <= c { temp1 } else { c };
    let temp3 = if temp2 <= d { temp2 } else { d };
    if temp3 <= e { temp3 } else { e }
}

spec fn ceil_div(a: int, b: int) -> int
    recommends a >= 0 && b >= 1
{
    (a + b - 1) / b
}

spec fn correct_result(n: int, a: int, b: int, c: int, d: int, e: int, result: int) -> bool
    recommends valid_input(n, a, b, c, d, e)
{
    let min_cap = min_capacity(a, b, c, d, e);
    let groups = ceil_div(n, min_cap);
    result == 4 + groups
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn solve(n: i8, a: i8, b: i8, c: i8, d: i8, e: i8) -> (result: i8)
    requires 
        valid_input(n as int, a as int, b as int, c as int, d as int, e as int)
    ensures 
        correct_result(n as int, a as int, b as int, c as int, d as int, e as int, result as int) &&
        result >= 5
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed assertion failures by proving division properties step by step */
    let min1 = if a <= b { a } else { b };
    let min2 = if min1 <= c { min1 } else { c };
    let min3 = if min2 <= d { min2 } else { d };
    let min_cap = if min3 <= e { min3 } else { e };
    
    assert(min_cap as int == min_capacity(a as int, b as int, c as int, d as int, e as int));
    assert(min_cap >= 1);
    
    // Calculate groups using i32 to avoid overflow
    let n_i32: i32 = n as i32;
    let min_cap_i32: i32 = min_cap as i32;
    let groups_i32: i32 = (n_i32 + min_cap_i32 - 1) / min_cap_i32;
    
    assert(groups_i32 >= 1) by {
        assert(n_i32 >= 1);
        assert(min_cap_i32 >= 1);
        assert(n_i32 + min_cap_i32 - 1 >= n_i32);
        // For positive integers a >= 1 and b >= 1, (a + b - 1) / b >= 1
        assert((n_i32 + min_cap_i32 - 1) >= min_cap_i32);
        assert((n_i32 + min_cap_i32 - 1) / min_cap_i32 >= 1);
    }
    
    // Ensure groups fits in i8 range
    assert(groups_i32 <= 127) by {
        assert(n <= 127);
        assert(min_cap >= 1);
        // (n + min_cap - 1) / min_cap <= n when min_cap >= 1
        assert((n_i32 + min_cap_i32 - 1) / min_cap_i32 <= n_i32);
        assert(groups_i32 <= n_i32);
        assert(n_i32 <= 127);
    }
    
    #[verifier::truncate]
    let groups: i8 = groups_i32 as i8;
    
    assert(groups as int == ceil_div(n as int, min_cap as int)) by {
        assert(groups_i32 as int == (n_i32 + min_cap_i32 - 1) as int / min_cap_i32 as int);
        assert(n_i32 as int == n as int);
        assert(min_cap_i32 as int == min_cap as int);
        assert((n_i32 + min_cap_i32 - 1) as int == n as int + min_cap as int - 1);
        assert(groups_i32 as int == (n as int + min_cap as int - 1) / (min_cap as int));
        assert(groups as int == groups_i32 as int);
    }
    
    // Check that result won't overflow i8
    assert(4 + groups <= 127) by {
        assert(groups <= 127);
        assert(4 + groups <= 4 + 127);
    }
    
    let result: i8 = 4 + groups;
    
    assert(correct_result(n as int, a as int, b as int, c as int, d as int, e as int, result as int)) by {
        assert(min_cap as int == min_capacity(a as int, b as int, c as int, d as int, e as int));
        assert(groups as int == ceil_div(n as int, min_cap as int));
        assert(result as int == 4 + groups as int);
    }
    
    assert(result >= 5) by {
        assert(groups >= 1);
        assert(result == 4 + groups);
    }
    
    result
}
// </vc-code>


}

fn main() {}