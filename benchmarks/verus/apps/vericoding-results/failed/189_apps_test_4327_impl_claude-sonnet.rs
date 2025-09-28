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
/* helper modified by LLM (iteration 4): fix lemma syntax */
proof fn lemma_arithmetic_bounds(a: i8, p: i8)
    requires
        valid_input(a as int, p as int)
    ensures
        0 <= a as int * 3 + p as int <= 600,
        a as int * 3 + p as int <= 127
{
    assert(a as int <= 100);
    assert(p as int <= 100);
    assert(a as int * 3 <= 300);
    assert(a as int * 3 + p as int <= 400);
}
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
    /* code modified by LLM (iteration 4): use ghost variables for int arithmetic */
    proof {
        lemma_arithmetic_bounds(a, p);
    }
    
    let ghost total_int = (a as int) * 3 + (p as int);
    
    proof {
        assert(total_int <= 400);
        assert(total_int <= 127);
    }
    
    let total = a * 3 + p;
    let pies = total / 2;
    pies
}
// </vc-code>


}

fn main() {}