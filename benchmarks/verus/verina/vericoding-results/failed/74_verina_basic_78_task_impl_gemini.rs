// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): added precondition lemmas */
proof fn lemma_sum_in_bounds(x: int, y: int)
    requires
        exists|r: i32| r as int == x + y,
    ensures
        i32::MIN <= x + y <= i32::MAX,
{
    let r = choose|r: i32| r as int == x + y;
    assert(i32::MIN <= r as int <= i32::MAX);
    assert(r as int == x + y);
}

proof fn lemma_diff_in_bounds(x: int, y: int)
    requires
        exists|r: i32| r as int == x - y,
    ensures
        i32::MIN <= x - y <= i32::MAX,
{
    let r = choose|r: i32| r as int == x - y;
    assert(i32::MIN <= r as int <= i32::MAX);
    assert(r as int == x - y);
}
// </vc-helpers>

// <vc-spec>
fn multiple_returns(x: i32, y: i32) -> (result: (i32, i32))
    ensures
        result.0 == x + y,
        result.1 + y == x,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): added assertions to prove no-overflow */
    assert(exists|r: (i32, i32)| r.0 as int == (x as int) + (y as int) && r.1 as int == (x as int) - (y as int));
    proof {
        lemma_sum_in_bounds(x as int, y as int);
        lemma_diff_in_bounds(x as int, y as int);
    }
    (x + y, x - y)
}
// </vc-code>

}
fn main() {}