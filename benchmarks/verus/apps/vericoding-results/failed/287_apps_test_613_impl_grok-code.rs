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
/* helper modified by LLM (iteration 3): use named returns to fix scoping issues with 'result' */
fn is_infinite(t: i8, a: i8, b: i8) -> (res: bool)
    ensures
        res == infinite_case(t as int, a as int, b as int),
{
    let res = a == t && a == b && a == 1;
    proof {
        assert(res == infinite_case(t as int, a as int, b as int));
    }
    res
}

/* helper modified by LLM (iteration 3): use named returns to fix scoping issues with 'result' */
fn is_two(t: i8, a: i8, b: i8) -> (res: bool)
    ensures
        res == two_solutions_case(t as int, a as int, b as int),
{
    let res = a == t && a == b && a != 1;
    proof {
        assert(res == two_solutions_case(t as int, a as int, b as int));
    }
    res
}

/* helper modified by LLM (iteration 5): cast to i32 for comparisons to fix int usage in runtime code */
fn is_zero(t: i8, a: i8, b: i8) -> (res: bool)
    ensures
        res == zero_solutions_case(t as int, a as int, b as int),
{
    let diff = a as i32 - b as i32;
    let denom = t as i32 - a as i32;
    let cond1 = ((t as i32) == 2i32) && ((a as i32) == 3i32) && ((b as i32) > 10000i32);
    let cond2 = a == t && a != b;
    let cond3 = a != t && denom != 0i32 && (diff % denom) == 0i32;
    let cond4 = a != t && denom != 0i32 && (diff % denom) != 0i32 && t == b;
    let res = cond1 || cond2 || cond3 || cond4;
    proof {
        if cond1 {
            assert(t as i32 <= 127i32);
            assert((t as int) == (t as i32));
            assert((a as int) == (a as i32));
            assert((b as int) == (b as i32));
        }
        if cond2 {
            assert(res == (a != b));
        }
        if cond3 {
            // assuming i32 % matches int % for these small values
            assert(res == zero_solutions_case(t as int, a as int, b as int));
        }
        if cond4 {
            assert(res == zero_solutions_case(t as int, a as int, b as int));
        }
        assert(res == zero_solutions_case(t as int, a as int, b as int));
    }
    res
}

/* helper modified by LLM (iteration 3): use named returns to fix scoping issues with 'result' */
fn is_one(t: i8, a: i8, b: i8) -> (res: bool)
    ensures
        res == one_solution_case(t as int, a as int, b as int),
{
    let diff = a as i32 - b as i32;
    let denom = t as i32 - a as i32;
    let res = a != t && denom != 0i32 && (diff % denom) != 0i32 && t != b;
    proof {
        assert(res == one_solution_case(t as int, a as int, b as int));
    }
    res
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
    /* code modified by LLM (iteration 4): implement main logic to check cases and return appropriate string */
    let res: String = if is_infinite(t, a, b) {
        "inf".to_string()
    } else if is_two(t, a, b) {
        "2".to_string()
    } else if is_zero(t, a, b) {
        "0".to_string()
    } else if is_one(t, a, b) {
        "1".to_string()
    } else {
        "1".to_string()
    };
    res
}
// </vc-code>


}

fn main() {}