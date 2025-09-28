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
/* helper modified by LLM (iteration 5): relate max_pies to total_pieces and arithmetic expression */
proof fn max_pies_eq(a: int, p: int)
    requires
        valid_input(a, p),
{
    proof {
        assert(total_pieces(a, p) == a * 3 + p);
        assert(max_pies(a, p) == total_pieces(a, p) / 2);
        assert(max_pies(a, p) == (a * 3 + p) / 2);
    }
}

/* helper modified by LLM (iteration 5): prove max_pies is non-negative */
proof fn max_pies_nonneg(a: int, p: int)
    requires
        valid_input(a, p),
{
    proof {
        assert(0 <= a);
        assert(0 <= p);
        assert(total_pieces(a, p) == a * 3 + p);
        assert(a * 3 + p >= 0);
        assert(total_pieces(a, p) >= 0);
        assert(max_pies(a, p) == total_pieces(a, p) / 2);
        assert(max_pies(a, p) >= 0);
    }
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
    /* code modified by LLM (iteration 5): compute using i16 temporaries and prove equality with spec */
    let total_i16: i16 = (a as i16) * 3 + (p as i16);
    let m_i16: i16 = total_i16 / 2;
    let pies: i8 = m_i16 as i8;
    proof {
        max_pies_eq(a as int, p as int);
        max_pies_nonneg(a as int, p as int);
        assert((total_i16 as int) == total_pieces(a as int, p as int));
        assert((m_i16 as int) == total_pieces(a as int, p as int) / 2);
        assert((pies as int) == (m_i16 as int));
        assert((pies as int) == max_pies(a as int, p as int));
    }
    pies
}

// </vc-code>


}

fn main() {}