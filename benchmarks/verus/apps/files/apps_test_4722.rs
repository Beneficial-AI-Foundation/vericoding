// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(a: int, b: int) -> bool {
    1 <= a <= 100 && 1 <= b <= 100
}

spec fn distribution_possible(a: int, b: int) -> bool {
    a % 3 == 0 || b % 3 == 0 || (a + b) % 3 == 0
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(a: i8, b: i8) -> (result: String)
    requires 
        valid_input(a as int, b as int)
    ensures 
        result@ == seq!['P', 'o', 's', 's', 'i', 'b', 'l', 'e'] <==> distribution_possible(a as int, b as int),
        result@ == seq!['P', 'o', 's', 's', 'i', 'b', 'l', 'e'] || result@ == seq!['I', 'm', 'p', 'o', 's', 's', 'i', 'b', 'l', 'e']
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}