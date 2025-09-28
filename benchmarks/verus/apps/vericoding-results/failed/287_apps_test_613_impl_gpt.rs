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
/* helper modified by LLM (iteration 3): string constructors with ensures remain simple and explicit */
fn make_zero() -> (s: String)
    ensures
        s@ == "0"@,
{
    "0".to_string()
}

/* helper modified by LLM (iteration 3): string constructors with ensures remain simple and explicit */
fn make_one() -> (s: String)
    ensures
        s@ == "1"@,
{
    "1".to_string()
}

/* helper modified by LLM (iteration 3): string constructors with ensures remain simple and explicit */
fn make_two() -> (s: String)
    ensures
        s@ == "2"@,
{
    "2".to_string()
}

/* helper modified by LLM (iteration 3): string constructors with ensures remain simple and explicit */
fn make_inf() -> (s: String)
    ensures
        s@ == "inf"@,
{
    "inf".to_string()
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
    /* code modified by LLM (iteration 3): branch directly by spec cases; avoid fragile modulo bridging assertions */
    if a == t && a == b && a == 1i8 {
        let s = make_inf();
        return s;
    } else if a == t && a == b {
        let s = make_two();
        return s;
    } else if a == t && a != b {
        let s = make_zero();
        return s;
    } else {
        // a != t case
        let da: i32 = (a as i32) - (b as i32);
        let db: i32 = (t as i32) - (a as i32);
        // since a != t, db != 0
        assert(db != 0);
        if da % db == 0 {
            let s = make_zero();
            return s;
        } else if t == b {
            let s = make_zero();
            return s;
        } else {
            let s = make_one();
            return s;
        }
    }
}
// </vc-code>


}

fn main() {}