// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(a: int, b: int, c: int) -> bool {
    1 <= a <= 10 && 1 <= b <= 10 && 1 <= c <= 10
}

spec fn can_form_haiku(a: int, b: int, c: int) -> bool {
    (a == 5 && b == 5 && c == 7) ||
    (a == 5 && b == 7 && c == 5) ||
    (a == 7 && b == 5 && c == 5)
}

spec fn valid_output(result: &str) -> bool {
    result == "YES" || result == "NO"
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): convert i8 to int */
spec fn i8_to_int(a: i8) -> int { a as int }

/* helper modified by LLM (iteration 4): equate i8 equality combos with can_form_haiku */
spec fn haiku_equiv(a: i8, b: i8, c: i8) -> bool {
    ((a as int) == 5 && (b as int) == 5 && (c as int) == 7) ||
    ((a as int) == 5 && (b as int) == 7 && (c as int) == 5) ||
    ((a as int) == 7 && (b as int) == 5 && (c as int) == 5)
    ==
    can_form_haiku(a as int, b as int, c as int)
}

// </vc-helpers>

// <vc-spec>
fn solve(a: i8, b: i8, c: i8) -> (result: &'static str)
    requires 
        valid_input(a as int, b as int, c as int),
    ensures 
        valid_output(result),
        (result == "YES") <==> can_form_haiku(a as int, b as int, c as int),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): proved equivalence inline without spec proof helper */
{
    let cond = (a == 5 && b == 5 && c == 7) ||
               (a == 5 && b == 7 && c == 5) ||
               (a == 7 && b == 5 && c == 5);

    proof {
        assert((a == 5) == ((a as int) == 5));
        assert((b == 5) == ((b as int) == 5));
        assert((c == 7) == ((c as int) == 7));
        assert((b == 7) == ((b as int) == 7));
        assert((c == 5) == ((c as int) == 5));
        assert((a == 7) == ((a as int) == 7));

        assert(cond ==
           (((a as int) == 5 && (b as int) == 5 && (c as int) == 7) ||
            ((a as int) == 5 && (b as int) == 7 && (c as int) == 5) ||
            ((a as int) == 7 && (b as int) == 5 && (c as int) == 5)));

        assert(cond == can_form_haiku(a as int, b as int, c as int));
    }

    if cond {
        "YES"
    } else {
        "NO"
    }
}

// </vc-code>


}

fn main() {}