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
    /* code modified by LLM (iteration 4): Fixed type mismatch by using string literals and to_string() to return proper String types instead of Seq<char> */
    let a_int = a as int;
    let b_int = b as int;
    let diff = if a_int >= b_int { a_int - b_int } else { b_int - a_int };
    let sum = a_int + b_int;
    let yes = (diff <= 1) && (sum > 0);
    proof {
        assert(yes == interval_exists(a_int, b_int));
    }
    if yes {
        "YES".to_string()
    } else {
        "NO".to_string()
    }
}
// </vc-code>


}

fn main() {}