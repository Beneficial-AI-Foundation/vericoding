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
proof fn lemma_case_classification(t: int, a: int, b: int)
    requires
        valid_input(t, a, b),
    ensures
        infinite_case(t, a, b) || two_solutions_case(t, a, b) || zero_solutions_case(t, a, b) || one_solution_case(t, a, b)
{
}

proof fn lemma_cases_exclusive(t: int, a: int, b: int)
    requires
        valid_input(t, a, b),
    ensures
        !(infinite_case(t, a, b) && two_solutions_case(t, a, b)),
        !(infinite_case(t, a, b) && zero_solutions_case(t, a, b)),
        !(infinite_case(t, a, b) && one_solution_case(t, a, b)),
        !(two_solutions_case(t, a, b) && zero_solutions_case(t, a, b)),
        !(two_solutions_case(t, a, b) && one_solution_case(t, a, b)),
        !(zero_solutions_case(t, a, b) && one_solution_case(t, a, b))
{
}

/* helper modified by LLM (iteration 5): fixed to handle all zero_solutions_case conditions */
proof fn lemma_zero_case_holds(t: i8, a: i8, b: i8)
    requires
        valid_input(t as int, a as int, b as int),
        a == t && a != b,
    ensures
        zero_solutions_case(t as int, a as int, b as int)
{
    assert(a as int == t as int && a as int != b as int);
}

/* helper modified by LLM (iteration 5): fixed precondition to match usage */
proof fn lemma_zero_case_holds_remainder(t: i8, a: i8, b: i8)
    requires
        valid_input(t as int, a as int, b as int),
        a != t,
        (a as int - b as int) % (t as int - a as int) == 0,
    ensures
        zero_solutions_case(t as int, a as int, b as int)
{
    assert(a as int != t as int && (a as int - b as int) % (t as int - a as int) == 0);
}

/* helper modified by LLM (iteration 5): fixed precondition to match usage */
proof fn lemma_zero_case_holds_t_equals_b(t: i8, a: i8, b: i8)
    requires
        valid_input(t as int, a as int, b as int),
        a != t,
        (a as int - b as int) % (t as int - a as int) != 0,
        t == b,
    ensures
        zero_solutions_case(t as int, a as int, b as int)
{
    assert(a as int != t as int && (a as int - b as int) % (t as int - a as int) != 0 && t as int == b as int);
}

proof fn lemma_one_case_holds(t: i8, a: i8, b: i8)
    requires
        valid_input(t as int, a as int, b as int),
        a != t,
        t != b,
        (a as int - b as int) % (t as int - a as int) != 0,
    ensures
        one_solution_case(t as int, a as int, b as int)
{
    assert(a as int != t as int && (a as int - b as int) % (t as int - a as int) != 0 && t as int != b as int);
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
    /* code modified by LLM (iteration 5): fixed to use int types for remainder calculation */
    proof {
        lemma_case_classification(t as int, a as int, b as int);
        lemma_cases_exclusive(t as int, a as int, b as int);
    }
    
    if a == t && a == b && a == 1 {
        "inf".to_string()
    } else if a == t && a == b && a != 1 {
        "2".to_string()
    } else if a == t && a != b {
        proof {
            lemma_zero_case_holds(t, a, b);
        }
        "0".to_string()
    } else {
        // a != t
        let remainder = (a as int - b as int) % (t as int - a as int);
        if remainder == 0 {
            proof {
                lemma_zero_case_holds_remainder(t, a, b);
            }
            "0".to_string()
        } else if t == b {
            proof {
                lemma_zero_case_holds_t_equals_b(t, a, b);
            }
            "0".to_string()
        } else {
            proof {
                lemma_one_case_holds(t, a, b);
            }
            "1".to_string()
        }
    }
}
// </vc-code>


}

fn main() {}