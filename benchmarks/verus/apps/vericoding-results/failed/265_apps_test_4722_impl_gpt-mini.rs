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
/* helper modified by LLM (iteration 5): trivial equivalence proof for distribution_possible */
proof fn distribution_possible_equiv(a: int, b: int)
    ensures
        distribution_possible(a, b) <==> (a % 3 == 0 || b % 3 == 0 || (a + b) % 3 == 0),
{
    proof {
        assert(distribution_possible(a, b) == (a % 3 == 0 || b % 3 == 0 || (a + b) % 3 == 0));
    }
}

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
    /* code modified by LLM (iteration 5): compute mod-3 condition and return "Possible"/"Impossible" with proof linking to spec predicate */
    let ai = a as int;
    let bi = b as int;
    let cond = ai % 3 == 0 || bi % 3 == 0 || (ai + bi) % 3 == 0;
    if cond {
        let s = String::from("Possible");
        proof {
            distribution_possible_equiv(ai, bi);
            assert(cond == distribution_possible(ai, bi));
        }
        s
    } else {
        let s = String::from("Impossible");
        proof {
            distribution_possible_equiv(ai, bi);
            assert(cond == distribution_possible(ai, bi));
        }
        s
    }
}
// </vc-code>


}

fn main() {}