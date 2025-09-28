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
/* helper modified by LLM (iteration 2): Helper to map a boolean condition to "YES"/"NO" with ensures linking */
fn choose_yes_no(cond: bool) -> (result: &'static str)
    ensures
        valid_output(result),
        (result == "YES") <==> cond,
{
    if cond {
        "YES"
    } else {
        "NO"
    }
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
{
    /* code modified by LLM (iteration 2): compute condition using i8 comparisons; prove equivalence to spec; avoid ghost ints in exec code */
    let cond = (a == 5i8 && b == 5i8 && c == 7i8)
        || (a == 5i8 && b == 7i8 && c == 5i8)
        || (a == 7i8 && b == 5i8 && c == 5i8);

    let res = choose_yes_no(cond);

    proof {
        assert((a == 5i8) <==> ((a as int) == 5));
        assert((a == 7i8) <==> ((a as int) == 7));
        assert((b == 5i8) <==> ((b as int) == 5));
        assert((b == 7i8) <==> ((b as int) == 7));
        assert((c == 5i8) <==> ((c as int) == 5));
        assert((c == 7i8) <==> ((c as int) == 7));
        assert(cond <==> can_form_haiku(a as int, b as int, c as int));
    }

    res
}
// </vc-code>


}

fn main() {}