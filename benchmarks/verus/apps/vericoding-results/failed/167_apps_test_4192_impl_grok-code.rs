// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(d: int, t: int, s: int) -> bool {
    1 <= d <= 10000 && 1 <= t <= 10000 && 1 <= s <= 10000
}

spec fn can_travel(d: int, t: int, s: int) -> bool {
    d <= t * s
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): No helpers needed */
// </vc-helpers>

// <vc-spec>
fn solve(d: i8, t: i8, s: i8) -> (result: &'static str)
    requires 
        valid_input(d as int, t as int, s as int),
    ensures 
        can_travel(d as int, t as int, s as int) ==> result == "Yes",
        !can_travel(d as int, t as int, s as int) ==> result == "No",
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Cast to u64 to avoid possible overflow and ensure verification */
    let di = d as u64;
    let ti = t as u64;
    let si = s as u64;
    let ts = ti * si;
    let result = if di <= ts { "Yes" } else { "No" };
    proof {
        let d_int = (d as int);
        let t_int = (t as int);
        let s_int = (s as int);
        assert(valid_input(d_int, t_int, s_int));
        assert(can_travel(d_int, t_int, s_int) == (d_int <= t_int * s_int));
        assert( d_int == di as int );
        assert( t_int == ti as int );
        assert( s_int == si as int );
        assert( t_int * s_int == ts as int );
        assert( result == if (d_int <= t_int * s_int) { "Yes" } else { "No" } );
    }
    result
}
// </vc-code>


}

fn main() {}