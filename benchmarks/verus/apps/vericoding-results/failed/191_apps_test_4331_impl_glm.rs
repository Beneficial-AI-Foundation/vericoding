// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(n: int) -> bool {
    100 <= n <= 999
}

spec fn contains_seven(n: int) -> bool
    recommends valid_input(n)
{
    (n % 10) == 7 || ((n / 10) % 10) == 7 || (n / 100) == 7
}

spec fn valid_output(result: Seq<char>) -> bool {
    result == "Yes\n"@ || result == "No\n"@
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn solve(n: i8) -> (result: Vec<char>)
    requires valid_input(n as int)
    ensures 
        valid_output(result@) &&
        ((result@ == "Yes\n"@) <==> contains_seven(n as int))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): compute digits in i8 and prove equivalence to spec */
    let units = n % 10;
    let tens = (n / 10) % 10;
    let hundreds = n / 100;
    let has_seven = units == 7 || tens == 7 || hundreds == 7;

    proof {
        let n_int = n as int;
        let ghost_units = n_int % 10;
        let ghost_tens = (n_int / 10) % 10;
        let ghost_hundreds = n_int / 100;
        assert(units == ghost_units);
        assert(tens == ghost_tens);
        assert(hundreds == ghost_hundreds);
        assert(has_seven == (ghost_units == 7 || ghost_tens == 7 || ghost_hundreds == 7));
        assert(contains_seven(n_int) == (ghost_units == 7 || ghost_tens == 7 || ghost_hundreds == 7));
        assert(has_seven == contains_seven(n_int));
    }

    if has_seven {
        vec!['Y', 'e', 's', '\n']
    } else {
        vec!['N', 'o', '\n']
    }
}
// </vc-code>


}

fn main() {}