// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn abs(x: int) -> int {
    if x >= 0 { x } else { -x }
}

spec fn alice_wins(x: int, y: int) -> bool {
    abs(x - y) > 1
}

spec fn brown_wins(x: int, y: int) -> bool {
    abs(x - y) <= 1
}

spec fn valid_input(x: int, y: int) -> bool {
    x >= 0 && y >= 0
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): relates the computed ad to spec abs(d) */
proof fn abs_equiv(d: int, ad: int)
    requires
        ad == if d >= 0 { d } else { -d },
    ensures
        ad == abs(d),
{
    if d >= 0 {
        assert(abs(d) == d);
        assert(ad == d);
    } else {
        assert(abs(d) == -d);
        assert(ad == -d);
    }
}
// </vc-helpers>

// <vc-spec>
fn determine_winner(x: i8, y: i8) -> (winner: &'static str)
    requires 
        valid_input(x as int, y as int),
    ensures 
        winner == "Alice" || winner == "Brown",
        (winner == "Alice") <==> alice_wins(x as int, y as int),
        (winner == "Brown") <==> brown_wins(x as int, y as int),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): compute winner using i8 arithmetic and perform ghost casts/proofs to relate to spec */
    let d_i8: i8 = x - y;
    let ad_i8: i8 = if d_i8 >= 0 { d_i8 } else { -d_i8 };
    let winner = if ad_i8 > 1 { "Alice" } else { "Brown" };
    proof {
        let xi: int = x as int;
        let yi: int = y as int;
        let d: int = xi - yi;
        let ad: int = if d >= 0 { d } else { -d };
        abs_equiv(d, ad);
        assert((d_i8 as int) == d);
        assert((ad_i8 as int) == ad);
        assert((ad_i8 as int) == abs(d));
        assert(((ad_i8 as int) > 1) <==> (ad > 1));
        assert((winner == "Alice") <==> (ad_i8 > 1));
        assert((winner == "Alice") <==> alice_wins(xi, yi));
        assert((winner == "Brown") <==> brown_wins(xi, yi));
    }
    winner
}
// </vc-code>


}

fn main() {}