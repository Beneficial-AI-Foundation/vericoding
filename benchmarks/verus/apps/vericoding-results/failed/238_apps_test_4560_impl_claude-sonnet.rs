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
/* helper modified by LLM (iteration 5): fixed lemma syntax by adding proof blocks */
proof fn lemma_mod_properties(n: int, a: int)
    requires
        1 <= n <= 10000,
        0 <= a <= 1000,
    ensures
        0 <= n % 500 <= 499,
{
}

proof fn lemma_payment_logic(n: int, a: int)
    requires
        1 <= n <= 10000,
        0 <= a <= 1000,
    ensures
        can_pay_exactly(n, a) <==> (n % 500 <= a),
{
}
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
    /* code modified by LLM (iteration 5): updated lemma calls to use proof function syntax */
    let remainder = (n as int) % 500;
    
    proof {
        lemma_mod_properties(n as int, a as int);
        lemma_payment_logic(n as int, a as int);
    }
    
    if remainder <= a as int {
        "Yes".to_string()
    } else {
        "No".to_string()
    }
}
// </vc-code>


}

fn main() {}