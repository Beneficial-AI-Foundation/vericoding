// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int) -> bool {
    100 <= n <= 999
}

spec fn valid_output(n: int, result: Seq<char>) -> bool
    recommends valid_input(n)
{
    result.len() == 6 && result.subrange(0, 3) == seq!['A', 'B', 'C'] && result.subrange(3, result.len() as int) == int_to_string(n)
}

spec fn int_to_string(n: int) -> Seq<char>
    recommends n >= 0
    decreases n
{
    if n == 0 {
        seq!['0']
    } else if n < 10 {
        seq![('0' as u8 + n as u8) as char]
    } else {
        int_to_string(n / 10).add(seq![('0' as u8 + (n % 10) as u8) as char])
    }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(n: i8) -> (result: Vec<char>)
    requires valid_input(n as int)
    ensures valid_output(n as int, result@)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}