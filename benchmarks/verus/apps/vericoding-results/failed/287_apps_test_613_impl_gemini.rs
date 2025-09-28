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
/* helper modified by LLM (iteration 5): use int for comparisons to match spec */
fn solve_a_eq_t(a: i8, b: i8) -> (res: String)
    requires
        valid_input(a as int, a as int, b as int),
    ensures
        valid_output(res),
        infinite_case(a as int, a as int, b as int) ==> res@ == "inf"@,
        two_solutions_case(a as int, a as int, b as int) ==> res@ == "2"@,
        zero_solutions_case(a as int, a as int, b as int) ==> res@ == "0"@,
{
    let a_int = a as int;
    let b_int = b as int;
    if a_int == b_int {
        if a_int == 1 {
            String::from_str("inf")
        } else {
            String::from_str("2")
        }
    } else {
        String::from_str("0")
    }
}

/* helper modified by LLM (iteration 5): use int for modulo arithmetic to match spec */
fn solve_a_ne_t(t: i8, a: i8, b: i8) -> (res: String)
    requires
        valid_input(t as int, a as int, b as int),
        a != t,
    ensures
        valid_output(res),
        zero_solutions_case(t as int, a as int, b as int) ==> res@ == "0"@,
        one_solution_case(t as int, a as int, b as int) ==> res@ == "1"@,
{
    let t_int = t as int;
    let a_int = a as int;
    let b_int = b as int;
    if (a_int - b_int) % (t_int - a_int) == 0 {
        String::from_str("0")
    } else if t_int == b_int {
        String::from_str("0")
    } else {
        String::from_str("1")
    }
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
{
    /* code modified by LLM (iteration 5): logic unchanged, relies on fixed helpers */
    if t == a {
        solve_a_eq_t(a, b)
    } else {
        solve_a_ne_t(t, a, b)
    }
}
// </vc-code>


}

fn main() {}