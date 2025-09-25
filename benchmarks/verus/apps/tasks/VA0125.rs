// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn split_on_space(s: Seq<char>) -> Seq<Seq<char>>;

spec fn valid_input(input: Seq<char>) -> bool {
    input.len() > 0 &&
    ({
        let trimmed = if input.len() > 0 && input[input.len() as int - 1] == '\n' { input.subrange(0, input.len() as int - 1) } else { input };
        let parts = split_on_space(trimmed);
        parts.len() >= 1
    })
}

spec fn get_expected_result(input: Seq<char>) -> Seq<char>
    recommends valid_input(input)
{
    let trimmed = if input.len() > 0 && input[input.len() as int - 1] == '\n' { input.subrange(0, input.len() as int - 1) } else { input };
    let parts = split_on_space(trimmed);
    if parts[parts.len() as int - 1] == seq!['m', 'o', 'n', 't', 'h'] {
        if parts[0] == seq!['3', '1'] { seq!['7', '\n'] }
        else if parts[0] == seq!['3', '0'] { seq!['1', '1', '\n'] }
        else { seq!['1', '2', '\n'] }
    } else {
        if parts[0] == seq!['5'] || parts[0] == seq!['6'] { seq!['5', '3', '\n'] }
        else { seq!['5', '2', '\n'] }
    }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(input: &str) -> (result: String)
    requires valid_input(input@)
    ensures result@ == get_expected_result(input@)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}