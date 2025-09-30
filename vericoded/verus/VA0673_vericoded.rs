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
{/* code modified by LLM (iteration 3): Implement the solve function using a while loop with invariants to build the result vector, and add a proof block at the end to assert the postcondition to help verification */
    let mut result: Vec<char> = Vec::with_capacity(10);
    result.push('2');
    result.push('0');
    result.push('1');
    result.push('8');
    let mut i: usize = 4;
    while i < 10
        invariant
            4 <= i <= 10,
            result@ == seq!['2', '0', '1', '8'].add(date_str@.subrange(4, i as int)),
            date_str@.len() == 10,
        decreases 10 - i
    {
        result.push(date_str[i]);
        i = i + 1;
    }
    proof {
        assert(result@.len() == 10);
        assert(result@.subrange(0, 4) == seq!['2', '0', '1', '8']);
        assert(result@.subrange(4, 10) == date_str@.subrange(4, 10));
        assert(result@ == seq!['2', '0', '1', '8'].add(date_str@.subrange(4, 10)));
    }
    result
}
// </vc-code>


}

fn main() {}