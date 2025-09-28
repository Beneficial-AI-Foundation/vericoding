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
/* helper modified by LLM (iteration 5): relate can_pay_exactly to modulus */
proof fn can_pay_mod_equiv(n: int, a: int)
    ensures
        can_pay_exactly(n, a) == (n % 500 <= a),
{
    proof {
        assert(can_pay_exactly(n, a) == (n % 500 <= a));
    }
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
    /* code modified by LLM (iteration 5): compute condition using i32 arithmetic and build string using alloc::string::String::from */
    let n32: i32 = n as i32;
    let a32: i32 = a as i32;
    let cond: bool = (n32 % 500) <= a32;
    let res = alloc::string::String::from(if cond { "Yes" } else { "No" });
    proof {
        let n_int: int = n32 as int;
        let a_int: int = a32 as int;
        can_pay_mod_equiv(n_int, a_int);
        assert((res@ == "Yes"@) <==> cond);
        assert((res@ == "Yes"@) <==> can_pay_exactly(n_int, a_int));
        assert(res@ == "Yes"@ || res@ == "No"@);
    }
    res
}
// </vc-code>


}

fn main() {}