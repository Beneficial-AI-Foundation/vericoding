// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(date_str: Seq<char>) -> bool {
    date_str.len() == 10 && date_str.subrange(0, 4) == seq!['2', '0', '1', '7']
}

spec fn valid_output(input: Seq<char>, output: Seq<char>) -> bool 
    recommends input.len() >= 4
{
    output == seq!['2', '0', '1', '8'].add(input.subrange(4, input.len() as int)) &&
    output.len() == 10 &&
    output.subrange(0, 4) == seq!['2', '0', '1', '8'] &&
    output.subrange(4, output.len() as int) == input.subrange(4, input.len() as int)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(date_str: Vec<char>) -> (result: Vec<char>)
    requires valid_input(date_str@)
    ensures valid_output(date_str@, result@)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}