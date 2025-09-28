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
    /* code modified by LLM (iteration 5): added overflow checks and assertions for verification */
    let a_int: int = a as int;
    let b_int: int = b as int;
    
    assert(0 <= a_int <= 100);
    assert(0 <= b_int <= 100);
    assert(a_int + b_int <= 200);
    
    let diff = if a >= b { (a - b) as int } else { (b - a) as int };
    
    assert(diff == abs_spec(a_int - b_int));
    
    if diff <= 1 && a_int + b_int > 0 {
        let result = String::from_str("YES");
        assert(result@ == "YES"@);
        assert(interval_exists(a_int, b_int));
        result
    } else {
        let result = String::from_str("NO");
        assert(result@ == "NO"@);
        assert(!interval_exists(a_int, b_int));
        result
    }
}
// </vc-code>


}

fn main() {}