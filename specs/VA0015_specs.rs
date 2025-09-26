// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(input: Seq<char>) -> bool {
    input.len() > 0
}

spec fn valid_output(result: Seq<char>) -> bool {
    result =~= seq!['K','u','r','o'] || result =~= seq!['S','h','i','r','o'] || result =~= seq!['K','a','t','i','e'] || result =~= seq!['D','r','a','w'] || result.len() == 0
}

spec fn optimal_score(ribbon: Seq<char>, turns: int) -> int 
    recommends ribbon.len() >= 0 && turns >= 0
{
    let max_freq = max_char_freq(ribbon);
    let length = ribbon.len() as int;
    if turns == 1 && max_freq == length {
        if max_freq > 0 { max_freq - 1 } else { 0 }
    } else if length < max_freq + turns {
        length
    } else {
        max_freq + turns
    }
}
spec fn max_char_freq(s: Seq<char>) -> int {
    0
}

spec fn split_lines(input: Seq<char>) -> Seq<Seq<char>> {
    seq![]
}

spec fn parse_int(s: Seq<char>) -> int {
    0
}

spec fn max3(a: int, b: int, c: int) -> int {
    if a >= b && a >= c { a } else if b >= c { b } else { c }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(input: Seq<char>) -> (result: Seq<char>)
    requires valid_input(input)
    ensures valid_output(result)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}