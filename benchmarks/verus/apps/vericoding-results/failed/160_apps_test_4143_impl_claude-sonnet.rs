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
/* helper modified by LLM (iteration 5): removed overly restrictive preconditions and added stronger bounds */
fn min_of_five(a: i8, b: i8, c: i8, d: i8, e: i8) -> (result: i8)
    requires
        a >= 1,
        b >= 1,
        c >= 1,
        d >= 1,
        e >= 1
    ensures
        result == min_capacity(a as int, b as int, c as int, d as int, e as int),
        result >= 1,
        result <= a,
        result <= b,
        result <= c,
        result <= d,
        result <= e
{
    let temp1 = if a <= b { a } else { b };
    let temp2 = if temp1 <= c { temp1 } else { c };
    let temp3 = if temp2 <= d { temp2 } else { d };
    if temp3 <= e { temp3 } else { e }
}

fn ceiling_divide(a: i8, b: i8) -> (result: i8)
    requires
        a >= 0,
        b >= 1,
        a <= 127,
        b <= 127,
        a + b <= 127
    ensures
        result == ceil_div(a as int, b as int),
        result >= 0
{
    proof {
        assert(a + b - 1 <= 126);
        assert((a + b - 1) as int == a as int + b as int - 1);
    }
    let intermediate = a + b - 1;
    intermediate / b
}

fn safe_add(a: i8, b: i8) -> (result: i8)
    requires
        a >= 0,
        b >= 0,
        a + b <= 127
    ensures
        result == a + b
{
    proof {
        assert((a + b) as int == a as int + b as int);
    }
    a + b
}
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
    /* code modified by LLM (iteration 5): removed assume statements and strengthened proof */
    let min_cap = min_of_five(a, b, c, d, e);
    
    proof {
        assert(min_cap >= 1);
        assert(min_cap <= a && min_cap <= b && min_cap <= c && min_cap <= d && min_cap <= e);
        assert(a >= 1 && b >= 1 && c >= 1 && d >= 1 && e >= 1);
        assert(min_cap <= 127);
        assert(n >= 1 && n <= 127);
        assert(n + min_cap <= 254);
        assert(n + min_cap <= 127);
    }
    
    let groups = ceiling_divide(n, min_cap);
    
    proof {
        assert(groups >= 0);
        assert(groups <= 127);
        assert(4 + groups <= 131);
        assert(4 + groups <= 127);
    }
    
    let result = safe_add(4, groups);
    result
}
// </vc-code>


}

fn main() {}