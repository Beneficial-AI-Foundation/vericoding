// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(x: int) -> bool {
    1 <= x <= 3000
}

spec fn correct_output(x: int, result: Seq<char>) -> bool {
    (x < 1200 ==> result == seq!['A', 'B', 'C', '\n']) &&
    (x >= 1200 ==> result == seq!['A', 'R', 'C', '\n'])
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn solve(x: i32) -> (result: Vec<char>)
    requires valid_input(x as int)
    ensures correct_output(x as int, result@)
// </vc-spec>
// <vc-code>
{
    let mut result = Vec::new();
    result.push('A');
    
    if x < 1200 {
        result.push('B');
    } else {
        result.push('R');
    }
    
    result.push('C');
    result.push('\n');
    
    assert(result@.len() == 4);
    assert(result@[0] == 'A');
    assert(result@[3] == '\n');
    
    if x < 1200 {
        assert(result@[1] == 'B');
        assert(result@[2] == 'C');
        assert(result@ == seq!['A', 'B', 'C', '\n']);
    } else {
        assert(result@[1] == 'R');
        assert(result@[2] == 'C');
        assert(result@ == seq!['A', 'R', 'C', '\n']);
    }
    
    result
}
// </vc-code>


}

fn main() {}