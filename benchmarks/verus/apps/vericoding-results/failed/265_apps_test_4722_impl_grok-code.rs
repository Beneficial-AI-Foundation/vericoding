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
    /* code modified by LLM (iteration 5): move int casts to proof block and compute modulo in exec types to fix compilation */
    let mod_a: i8 = a % 3;
    let mod_b: i8 = b % 3;
    let sum: i32 = a as i32 + b as i32;
    let mod_sum: i32 = sum % 3;
    let is_possible_exec: bool = mod_a == 0 || mod_b == 0 || (mod_sum == 0);
    proof {
        let ai: int = a as int;
        let bi: int = b as int;
        assert(ai % 3 == mod_a as int);
        assert(bi % 3 == mod_b as int);
        assert((ai + bi) % 3 == mod_sum as int);
        assert(is_possible_exec <==> distribution_possible(ai, bi));
    }
    if is_possible_exec {
        "Possible".into()
    } else {
        "Impossible".into()
    }
}
// </vc-code>


}

fn main() {}