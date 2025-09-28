// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(input: Seq<char>) -> bool {
    input.len() == 3 && forall|i: int| 0 <= i < input.len() ==> input[i] == 'A' || input[i] == 'B'
}

spec fn bus_service_exists(input: Seq<char>) -> bool
    recommends valid_input(input)
{
    input[0] != input[1] || input[1] != input[2]
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(input: Vec<char>) -> (result: Vec<char>)
    requires
        valid_input(input@),
    ensures
        result@ == seq!['Y', 'e', 's'] <==> bus_service_exists(input@),
        result@ == seq!['Y', 'e', 's'] || result@ == seq!['N', 'o'],
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}