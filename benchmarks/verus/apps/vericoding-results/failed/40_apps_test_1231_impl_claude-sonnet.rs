// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(a: int, b: int) -> bool {
    0 <= a <= 100 && 0 <= b <= 100
}

spec fn valid_output(result: String) -> bool {
    result@ == "YES"@ || result@ == "NO"@
}

spec fn interval_exists(a: int, b: int) -> bool {
    abs_spec(a - b) <= 1 && a + b > 0
}

spec fn abs_spec(x: int) -> int {
    if x >= 0 { x } else { -x }
}
// </vc-preamble>

// <vc-helpers>
proof fn lemma_abs_spec_properties(x: int)
    ensures
        abs_spec(x) >= 0,
        abs_spec(x) >= x,
        abs_spec(x) >= -x,
        x >= 0 ==> abs_spec(x) == x,
        x < 0 ==> abs_spec(x) == -x
{
}

proof fn lemma_interval_decision(a: int, b: int)
    requires
        valid_input(a, b)
    ensures
        interval_exists(a, b) <==> (abs_spec(a - b) <= 1 && a + b > 0)
{
}

/* helper modified by LLM (iteration 5): made function spec only */
spec fn compute_abs_diff(a: int, b: int) -> int
{
    abs_spec(a - b)
}

/* helper modified by LLM (iteration 5): add bounds checking lemma */
proof fn lemma_no_overflow(a: i8, b: i8)
    requires
        valid_input(a as int, b as int)
    ensures
        a as int + b as int <= 200,
        -100 <= a as int - b as int <= 100
{
}
// </vc-helpers>

// <vc-spec>
fn solve(a: i8, b: i8) -> (result: String)
    requires 
        valid_input(a as int, b as int)
    ensures 
        valid_output(result) &&
        ((result@ == "YES"@) <==> interval_exists(a as int, b as int))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): use checked arithmetic and add overflow proof */
    proof {
        lemma_no_overflow(a, b);
        lemma_abs_spec_properties(a as int - b as int);
        lemma_interval_decision(a as int, b as int);
    }
    
    let ghost abs_diff: int = compute_abs_diff(a as int, b as int);
    let ghost sum: int = a as int + b as int;
    
    let exec_diff = if a >= b { a - b } else { b - a };
    let exec_sum = (a as i32) + (b as i32);
    
    proof {
        assert(exec_diff as int == abs_diff);
        assert(exec_sum as int == sum);
        assert(interval_exists(a as int, b as int) <==> (abs_diff <= 1 && sum > 0));
    }
    
    if exec_diff <= 1 && exec_sum > 0 {
        "YES".to_string()
    } else {
        "NO".to_string()
    }
}
// </vc-code>


}

fn main() {}