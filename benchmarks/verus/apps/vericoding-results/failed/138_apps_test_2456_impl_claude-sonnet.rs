// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(n: int, r: int) -> bool {
    n >= 1 && r >= 1
}

spec fn expected_result(n: int, r: int) -> int {
    if valid_input(n, r) {
        let k = if r < n - 1 { r } else { n - 1 };
        k * (k + 1) / 2 + if r >= n { 1int } else { 0int }
    } else {
        0int
    }
}

fn solve_shapes(n: i8, r: i8) -> (result: i8)
    requires valid_input(n as int, r as int)
    ensures result as int == expected_result(n as int, r as int)
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed missing braces syntax error */
lemma lemma_k_bounds(n: int, r: int)
    requires valid_input(n, r)
    ensures
        let k = if r < n - 1 { r } else { n - 1 };
        k >= 0,
        k < n,
        k <= r,
        k * (k + 1) / 2 <= 127
{
    let k = if r < n - 1 { r } else { n - 1 };
    assert(n >= 1 && r >= 1);
    assert(k >= 0);
    assert(k < n);
    assert(k <= 127);
    assert(k * (k + 1) <= k * (k + k)) by {
        assert(1 <= k);
    }
    assert(k * (k + 1) / 2 <= k * k) by {
        assert(k * (k + 1) <= 2 * k * k);
    }
    assert(k <= 127 ==> k * k <= 127 * 127);
    assert(k * (k + 1) / 2 <= 127);
}
// </vc-helpers>

// <vc-spec>
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed compilation error by correcting lemma definition */
    let k_int = if (r as int) < (n as int) - 1 { r as int } else { (n as int) - 1 };
    
    proof {
        lemma_k_bounds(n as int, r as int);
    }
    
    let k = if r < n - 1 { r } else { n - 1 };
    let triangular = k * (k + 1) / 2;
    let bonus = if r >= n { 1 } else { 0 };
    
    proof {
        assert(k as int == k_int);
        assert(triangular as int == k_int * (k_int + 1) / 2);
        assert(bonus as int == if (r as int) >= (n as int) { 1int } else { 0int });
        assert((triangular + bonus) as int == expected_result(n as int, r as int));
    }
    
    triangular + bonus
}
// </vc-code>


}

fn main() {}