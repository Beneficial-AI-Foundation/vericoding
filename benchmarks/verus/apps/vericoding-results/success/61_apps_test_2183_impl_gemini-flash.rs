// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_brother_numbers(a: int, b: int) -> bool {
    1 <= a <= 3 && 1 <= b <= 3 && a != b
}

spec fn late_brother(a: int, b: int) -> int
    recommends valid_brother_numbers(a, b)
{
    6 - a - b
}

spec fn is_valid_result(a: int, b: int, result: int) -> bool {
    valid_brother_numbers(a, b) ==> 
        (1 <= result <= 3 && result != a && result != b)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): The type `int` can only be used in ghost context. `late_brother_exec` is an `exec` function. So, we convert to `i8` */
fn late_brother_exec(a: i8, b: i8) -> (result: i8)
    requires
        valid_brother_numbers(a as int, b as int),
    ensures
        result as int == late_brother(a as int, b as int),
{
    (6 - a - b) as i8
}
// </vc-helpers>

// <vc-spec>
fn solve(a: i8, b: i8) -> (result: i8)
    requires 
        valid_brother_numbers(a as int, b as int)
    ensures 
        is_valid_result(a as int, b as int, result as int) &&
        result as int == late_brother(a as int, b as int)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Call `late_brother_exec` with `i8` args and return `i8` result */
{
    let result = late_brother_exec(a, b);
    result
}
// </vc-code>


}

fn main() {}