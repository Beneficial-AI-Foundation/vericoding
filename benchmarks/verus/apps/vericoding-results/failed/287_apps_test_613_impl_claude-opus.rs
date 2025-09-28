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
    /* code modified by LLM (iteration 5): Fixed return values for zero_solutions_case and one_solution_case */
    if a == t && a == b && a == 1 {
        // infinite_case
        return "inf".to_string();
    } else if a == t && a == b && a != 1 {
        // two_solutions_case
        return "2".to_string();
    } else if t == 2 && a == 3 && b > 100 {
        // zero_solutions_case: special case (using 100 instead of 10000 for i8)
        return "0".to_string();
    } else if a == t && a != b {
        // zero_solutions_case
        return "0".to_string();
    } else if a != t {
        let diff_ab = a - b;
        let diff_ta = t - a;
        if diff_ab % diff_ta == 0 {
            // zero_solutions_case: (a != t && (a - b) % (t - a) == 0)
            return "0".to_string();
        } else if t == b {
            // zero_solutions_case: (a != t && (a - b) % (t - a) != 0 && t == b)
            return "0".to_string();
        } else {
            // one_solution_case: (a != t && (a - b) % (t - a) != 0 && t != b)
            return "1".to_string();
        }
    } else {
        // This should be unreachable given the cases above
        return "0".to_string();
    }
}
// </vc-code>


}

fn main() {}