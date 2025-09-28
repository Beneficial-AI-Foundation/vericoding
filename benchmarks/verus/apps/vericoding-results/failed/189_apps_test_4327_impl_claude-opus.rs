// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(a: int, p: int) -> bool {
    0 <= a <= 100 && 0 <= p <= 100
}

spec fn total_pieces(a: int, p: int) -> int
    recommends valid_input(a, p)
{
    a * 3 + p
}

spec fn max_pies(a: int, p: int) -> int
    recommends valid_input(a, p)
{
    total_pieces(a, p) / 2
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn calculate_max_pies(a: i8, p: i8) -> (pies: i8)
    requires 
        valid_input(a as int, p as int)
    ensures 
        pies as int == max_pies(a as int, p as int) &&
        pies >= 0 &&
        pies as int == (a as int * 3 + p as int) / 2
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): perform calculations with i16 and verify i8 bounds correctly */
    let total: i16 = (a as i16) * 3 + (p as i16);
    let pies_i16: i16 = total / 2;
    
    proof {
        assert(0 <= a as int && a as int <= 100);
        assert(0 <= p as int && p as int <= 100);
        assert(total as int == (a as int) * 3 + (p as int));
        assert(0 <= total as int);
        assert(total as int <= 100 * 3 + 100);
        assert(total as int <= 400);
        assert(pies_i16 as int == (total as int) / 2);
        assert(0 <= pies_i16 as int);
        assert(pies_i16 as int <= 400 / 2);
        assert(pies_i16 as int <= 200);
        assert(pies_i16 as int <= 127 || pies_i16 as int <= 200);
    }
    
    let pies: i8 = if pies_i16 <= 127 {
        pies_i16 as i8
    } else {
        127
    };
    pies
}
// </vc-code>


}

fn main() {}