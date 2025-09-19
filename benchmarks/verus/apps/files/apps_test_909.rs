// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(a: int, b: int, c: int) -> bool {
    1 <= a <= 10 && 1 <= b <= 10 && 1 <= c <= 10
}

spec fn all_expressions(a: int, b: int, c: int) -> Seq<int> {
    seq![a * b * c, a + b * c, a * b + c, a * (b + c), (a + b) * c, a + b + c]
}

spec fn max_expression(a: int, b: int, c: int) -> int
    recommends valid_input(a, b, c)
{
    let exprs = all_expressions(a, b, c);
    if exprs[0] >= exprs[1] && exprs[0] >= exprs[2] && exprs[0] >= exprs[3] && exprs[0] >= exprs[4] && exprs[0] >= exprs[5] { exprs[0] }
    else if exprs[1] >= exprs[2] && exprs[1] >= exprs[3] && exprs[1] >= exprs[4] && exprs[1] >= exprs[5] { exprs[1] }
    else if exprs[2] >= exprs[3] && exprs[2] >= exprs[4] && exprs[2] >= exprs[5] { exprs[2] }
    else if exprs[3] >= exprs[4] && exprs[3] >= exprs[5] { exprs[3] }
    else if exprs[4] >= exprs[5] { exprs[4] }
    else { exprs[5] }
}

spec fn is_max_of_all_expressions(result: int, a: int, b: int, c: int) -> bool
    recommends valid_input(a, b, c)
{
    let exprs = all_expressions(a, b, c);
    exprs.contains(result) && forall|i: int| 0 <= i < exprs.len() ==> result >= exprs[i]
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(a: i8, b: i8, c: i8) -> (result: i8)
    requires 
        valid_input(a as int, b as int, c as int),
    ensures 
        is_max_of_all_expressions(result as int, a as int, b as int, c as int),
        result as int == max_expression(a as int, b as int, c as int),
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}