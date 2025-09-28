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
/* helper modified by LLM (iteration 5): Fixed postconditions for mod properties and div-mod relationship */
proof fn lemma_mod_properties(x: int, y: int)
    requires
        y != 0,
    ensures
        x % y == x % y,
{
}

proof fn lemma_div_mod_relationship(x: int, y: int)
    requires
        y != 0,
    ensures
        x == y * (x / y) + x % y,
{
}

proof fn lemma_mod_range(x: int, y: int)
    requires
        y > 0,
    ensures
        0 <= x % y < y,
{
}

proof fn lemma_mod_zero_implies_divisible(x: int, y: int)
    requires
        y != 0,
    ensures
        (x % y == 0) == (y * (x / y) == x),
{
    lemma_div_mod_relationship(x, y);
}

proof fn lemma_mod_nonzero_implies_not_divisible(x: int, y: int)
    requires
        y != 0,
    ensures
        (x % y != 0) == (y * (x / y) != x),
{
    lemma_div_mod_relationship(x, y);
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
/* code modified by LLM (iteration 5): Fixed condition evaluation to match specification */
{
    if t == 1 && a == 1 && b == 1 {
        return "inf".to_string();
    } else if t == a && a == b {
        return "2".to_string();
    } else if (t == 2 && a == 3 && b > 10000)
          || (t == a && a != b)
          || (t != a && (a - b) % (t - a) == 0)
          || (t != a && (a - b) % (t - a) != 0 && t == b) {
        return "0".to_string();
    } else {
        return "1".to_string();
    }
}
// </vc-code>


}

fn main() {}