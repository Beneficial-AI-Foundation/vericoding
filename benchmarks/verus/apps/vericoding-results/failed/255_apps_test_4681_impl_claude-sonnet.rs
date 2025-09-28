// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn lucas(n: int) -> int
    recommends n >= 0
    decreases n
{
    if n <= 0 {
        2
    } else if n == 1 {
        1
    } else {
        lucas(n - 1) + lucas(n - 2)
    }
}

spec fn valid_input(n: int) -> bool {
    1 <= n <= 86
}
// </vc-preamble>

// <vc-helpers>
lemma lemma_lucas_bounds(n: int)
    requires 1 <= n <= 86
    ensures lucas(n) <= 2_971_215_073
{
    assert(lucas(1) == 1);
    assert(lucas(2) == 3);
    assert(lucas(3) == 4);
    assert(lucas(4) == 7);
    assert(lucas(5) == 11);
    if n <= 5 {
        return;
    }
    let mut i = 6;
    while i <= n
        invariant
            6 <= i <= n + 1,
            lucas(i - 1) <= 2_971_215_073
        decreases n - i
    {
        assert(lucas(i) == lucas(i - 1) + lucas(i - 2));
        i = i + 1;
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8) -> (result: i8)
    requires valid_input(n as int)
    ensures result as int == lucas(n as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed lemma call syntax */
    if n <= 0 {
        return 2;
    } else if n == 1 {
        return 1;
    }
    
    let mut prev_prev = 2i8;
    let mut prev = 1i8;
    let mut i = 2;
    
    while i <= n
        invariant
            2 <= i <= n + 1,
            prev_prev as int == lucas((i - 2) as int),
            prev as int == lucas((i - 1) as int)
        decreases n - i
    {
        proof {
            lemma_lucas_bounds(i as int);
        }
        let temp = prev + prev_prev;
        prev_prev = prev;
        prev = temp;
        i = i + 1;
    }
    
    prev
}
// </vc-code>


}

fn main() {}