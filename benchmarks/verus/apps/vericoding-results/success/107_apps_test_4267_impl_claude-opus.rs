// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_temperature(temp: int) -> bool {
    -40 <= temp <= 40
}

spec fn expected_output(temp: int) -> Seq<char> {
    if temp >= 30 { seq!['Y', 'e', 's', '\n'] } else { seq!['N', 'o', '\n'] }
}

spec fn correct_output(temp: int, output: Seq<char>) -> bool {
    output == expected_output(temp)
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn solve(x: i8) -> (result: Vec<u8>)
    requires valid_temperature(x as int)
    ensures correct_output(x as int, result@.map(|i: int, b: u8| b as char))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): Fixed character literal syntax */
    let mut result = Vec::new();
    
    if x >= 30 {
        result.push('Y' as u8);
        result.push('e' as u8);
        result.push('s' as u8);
        result.push('\n' as u8);
    } else {
        result.push('N' as u8);
        result.push('o' as u8);
        result.push('\n' as u8);
    }
    
    assert(result@.len() == expected_output(x as int).len());
    assert(result@.map(|i: int, b: u8| b as char) == expected_output(x as int));
    
    result
}
// </vc-code>


}

fn main() {}