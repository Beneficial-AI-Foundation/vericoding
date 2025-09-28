// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(a: int, b: int) -> bool {
    1 <= a <= 100 && 1 <= b <= 100
}

spec fn distribution_possible(a: int, b: int) -> bool {
    a % 3 == 0 || b % 3 == 0 || (a + b) % 3 == 0
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): construct the exact "Possible" string via from_chars */
fn make_possible() -> (result: String)
    ensures
        result@ == seq!['P', 'o', 's', 's', 'i', 'b', 'l', 'e'],
{
    String::from_chars(seq!['P', 'o', 's', 's', 'i', 'b', 'l', 'e'])
}

/* helper modified by LLM (iteration 5): construct the exact "Impossible" string via from_chars */
fn make_impossible() -> (result: String)
    ensures
        result@ == seq!['I', 'm', 'p', 'o', 's', 's', 'i', 'b', 'l', 'e'],
{
    String::from_chars(seq!['I', 'm', 'p', 'o', 's', 's', 'i', 'b', 'l', 'e'])
}
// </vc-helpers>

// <vc-spec>
fn solve(a: i8, b: i8) -> (result: String)
    requires 
        valid_input(a as int, b as int)
    ensures 
        result@ == seq!['P', 'o', 's', 's', 'i', 'b', 'l', 'e'] <==> distribution_possible(a as int, b as int),
        result@ == seq!['P', 'o', 's', 's', 'i', 'b', 'l', 'e'] || result@ == seq!['I', 'm', 'p', 'o', 's', 's', 'i', 'b', 'l', 'e']
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): decide using arithmetic on i32 and return precisely constructed strings */
    let ai32: i32 = a as i32;
    let bi32: i32 = b as i32;

    let possible: bool = (ai32 % 3 == 0) || (bi32 % 3 == 0) || ((ai32 + bi32) % 3 == 0);

    proof {
        let ghost ai: int = a as int;
        let ghost bi: int = b as int;
        assert(1 <= ai && 1 <= bi);
        assert(
            distribution_possible(ai, bi)
            <==>
            ((ai % 3 == 0) || (bi % 3 == 0) || ((ai + bi) % 3 == 0))
        );
    }

    if possible {
        make_possible()
    } else {
        make_impossible()
    }
}
// </vc-code>


}

fn main() {}