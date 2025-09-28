// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, a: int) -> bool {
    1 <= n <= 10000 && 0 <= a <= 1000
}

spec fn can_pay_exactly(n: int, a: int) -> bool {
    n % 500 <= a
}

spec fn valid_output(result: String) -> bool {
    result@ == "Yes"@ || result@ == "No"@
}
// </vc-preamble>

// <vc-helpers>

proof fn can_pay_theorem(n: int, a: int)
    requires
        valid_input(n, a),
    ensures
        can_pay_exactly(n, a) <==> n % 500 <= a
{
    // The definition directly matches the specification
    assert(n % 500 <= a ==> can_pay_exactly(n, a));
    assert(can_pay_exactly(n, a) ==> n % 500 <= a);
}

/* helper modified by LLM (iteration 5): simplified theorem proof */
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, a: i8) -> (result: String)
    requires 
        valid_input(n as int, a as int)
    ensures 
        valid_output(result) &&
        ((result@ == "Yes"@) <==> can_pay_exactly(n as int, a as int))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fix postcondition by ensuring proper type conversion */
    let n_int = n as int;
    let a_int = a as int;
    
    proof {
        can_pay_theorem(n_int, a_int);
    }
    
    let remainder = (n_int % 500) as i32;
    let a_i32 = a_int as i32;
    
    if remainder <= a_i32 {
        "Yes".to_string()
    } else {
        "No".to_string()
    }
}
// </vc-code>


}

fn main() {}