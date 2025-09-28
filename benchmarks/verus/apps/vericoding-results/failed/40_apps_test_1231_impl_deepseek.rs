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

proof fn decision_correctness(a: int, b: int)
    requires
        valid_input(a, b)
    ensures
        interval_exists(a, b) == (abs_spec(a - b) <= 1 && a + b > 0)
{
}

proof fn abs_nonnegative(x: int)
    ensures
        abs_spec(x) >= 0
{
}

proof fn safe_arithmetic(a: i8, b: i8)
    requires
        valid_input(a as int, b as int)
    ensures
        (a as int + b as int) > 0 == (a as i16 + b as i16 > 0)
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
    /* code modified by LLM (iteration 5): fixed arithmetic overflow and ensured correct output */
    safe_arithmetic(a, b);
    let a_int = a as i16;
    let b_int = b as i16;
    let diff = if a_int > b_int { a_int - b_int } else { b_int - a_int };
    
    if diff <= 1 && a_int + b_int > 0 {
        "YES".to_string()
    } else {
        "NO".to_string()
    }
}
// </vc-code>


}

fn main() {}