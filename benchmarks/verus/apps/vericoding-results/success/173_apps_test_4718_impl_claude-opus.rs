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
    /* code modified by LLM (iteration 2): added decreases clause to while loop */
    let mut result = Vec::new();
    result.push('2');
    result.push('0');
    result.push('1');
    result.push('8');
    
    let mut i = 4;
    while i < date_str.len()
        invariant
            4 <= i <= date_str.len(),
            date_str@.len() == 10,
            result@.len() == i,
            result@ == seq!['2', '0', '1', '8'].add(date_str@.subrange(4, i as int)),
            valid_input(date_str@),
        decreases date_str.len() - i
    {
        result.push(date_str[i]);
        i = i + 1;
    }
    
    assert(result@.len() == 10);
    assert(result@.subrange(0, 4) == seq!['2', '0', '1', '8']);
    assert(result@.subrange(4, 10) == date_str@.subrange(4, 10));
    
    result
}
// </vc-code>


}

fn main() {}