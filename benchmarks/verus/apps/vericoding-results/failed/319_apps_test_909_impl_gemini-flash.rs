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
/* helper modified by LLM (iteration 5): The helper `max_of_two` is correctly defined as a spec function. */
spec fn max_of_two(x: int, y: int) -> int { if x >= y { x } else { y } }
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
/* code modified by LLM (iteration 5): Corrected `ghost int` type to `ghost<int>` for the ghost variables. */
{
    // Use ghost variables for calculations to avoid 'nat'/'int' type errors in concrete code
    let a_ghost: ghost<int> = a as int;
    let b_ghost: ghost<int> = b as int;
    let c_ghost: ghost<int> = c as int;

    let val1_ghost: ghost<int> = a_ghost * b_ghost * c_ghost;
    let val2_ghost: ghost<int> = a_ghost + b_ghost * c_ghost;
    let val3_ghost: ghost<int> = a_ghost * b_ghost + c_ghost;
    let val4_ghost: ghost<int> = a_ghost * (b_ghost + c_ghost);
    let val5_ghost: ghost<int> = (a_ghost + b_ghost) * c_ghost;
    let val6_ghost: ghost<int> = a_ghost + b_ghost + c_ghost;

    let max_val: ghost<int> = max_of_two(val1_ghost, 
                                max_of_two(val2_ghost, 
                                    max_of_two(val3_ghost, 
                                        max_of_two(val4_ghost, 
                                            max_of_two(val5_ghost, val6_ghost)))));

    proof {
        let exprs = all_expressions(a_ghost, b_ghost, c_ghost);
        assert(exprs[0] == val1_ghost);
        assert(exprs[1] == val2_ghost);
        assert(exprs[2] == val3_ghost);
        assert(exprs[3] == val4_ghost);
        assert(exprs[4] == val5_ghost);
        assert(exprs[5] == val6_ghost);
        assert(max_val == max_expression(a_ghost, b_ghost, c_ghost));
    }

    max_val as i8
}
// </vc-code>


}

fn main() {}