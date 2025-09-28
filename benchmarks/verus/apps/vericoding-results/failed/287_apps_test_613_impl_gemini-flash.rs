// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(t: int, a: int, b: int) -> bool {
    t > 0 && a > 0 && b > 0
}

spec fn valid_output(res: String) -> bool {
    res@ == "0"@ || res@ == "1"@ || res@ == "2"@ || res@ == "inf"@
}

spec fn infinite_case(t: int, a: int, b: int) -> bool {
    a == t && a == b && a == 1
}

spec fn two_solutions_case(t: int, a: int, b: int) -> bool {
    a == t && a == b && a != 1
}

spec fn zero_solutions_case(t: int, a: int, b: int) -> bool {
    (t == 2 && a == 3 && b > 10000) ||
    (a == t && a != b) ||
    (a != t && (a - b) % (t - a) == 0) ||
    (a != t && (a - b) % (t - a) != 0 && t == b)
}

spec fn one_solution_case(t: int, a: int, b: int) -> bool {
    a != t && (a - b) % (t - a) != 0 && t != b
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): no change needed */
spec fn divides(divisor: int, dividend: int) -> bool {
    dividend % divisor == 0
}
// </vc-helpers>

// <vc-spec>
fn solve(t: i8, a: i8, b: i8) -> (res: String)
    requires 
        valid_input(t as int, a as int, b as int),
    ensures 
        valid_output(res),
        infinite_case(t as int, a as int, b as int) ==> res@ == "inf"@,
        two_solutions_case(t as int, a as int, b as int) ==> res@ == "2"@,
        zero_solutions_case(t as int, a as int, b as int) ==> res@ == "0"@,
        one_solution_case(t as int, a as int, b as int) ==> res@ == "1"@
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): removed ghost casts in if conditions to prevent compilation errors */
{
    let t_int = t as int;
    let a_int = a as int;
    let b_int = b as int;

    if infinite_case(t_int, a_int, b_int) {
        return String::from("inf");
    }
    if two_solutions_case(t_int, a_int, b_int) {
        return String::from("2");
    }
    if zero_solutions_case(t_int, a_int, b_int) {
        return String::from("0");
    }
    return String::from("1"); // If none of the above, it must be the one_solution_case
}
// </vc-code>


}

fn main() {}