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
/* helper modified by LLM (iteration 3): prove product of two positive ints >= 1 */
proof fn lemma_mul_positive(t: int, s: int)
    requires
        1 <= t <= 10000,
        1 <= s <= 10000,
    ensures
        t * s >= 1,
{
    let k = s - 1;
    assert(k >= 0);
    assert(t >= 1);
    assert(t >= 0);
    assert(t * s == t + t * k);
    assert(t * k >= 0);
    assert(t + t * k >= t);
    assert(t >= 1);
    assert(t * s >= 1);
}

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
    /* code modified by LLM (iteration 3): compare using spec-level ints to match specification and avoid overflow */
    let di = d as int;
    let ti = t as int;
    let si = s as int;
    if di <= ti * si {
        "Yes"
    } else {
        "No"
    }
}

// </vc-code>


}

fn main() {}