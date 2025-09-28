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
/* helper modified by LLM (iteration 5): lemma to prove arithmetic safety and property preservation */
fn lemma_arithmetic_safety(d: i8, t: i8, s: i8)
    requires
        valid_input(d as int, t as int, s as int),
    ensures
        t as int * s as int <= i8::MAX,
        (d as int <= (t as int) * (s as int)) == (d <= t * s),
{
    assert(1 <= t <= 10000);
    assert(1 <= s <= 10000);
    assert(t as int * s as int <= 10000 * 10000);
    assert(10000 * 10000 == 100000000);
    assert(100000000 <= i8::MAX);
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
    /* code modified by LLM (iteration 5): use lemma to prove arithmetic safety before comparison */
    proof {
        lemma_arithmetic_safety(d, t, s);
    }
    
    if d <= t * s {
        "Yes"
    } else {
        "No"
    }
}
// </vc-code>


}

fn main() {}