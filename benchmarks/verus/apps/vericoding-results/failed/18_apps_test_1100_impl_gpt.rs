// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int) -> bool {
    n >= 3
}

spec fn min_jumps(n: int) -> int
    recommends valid_input(n)
{
    (n - 2) * (n - 2)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): simple square spec function to aid reasoning */
spec fn sq(x: int) -> int {
    x * x
}

/* helper modified by LLM (iteration 2): trivial lemma revealing min_jumps definition */
proof fn lemma_min_jumps(n: int)
    requires
        valid_input(n),
    ensures
        min_jumps(n) == (n - 2) * (n - 2),
{
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8) -> (result: i8)
    requires valid_input(n as int)
    ensures result as int == min_jumps(n as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): avoid exec 'int' variables; compute using i8 loop and relate to spec via casts */
    let k: i8 = n - 2;
    let mut i: i8 = 0;
    let mut acc: i8 = 0;
    while i < k
        invariant
            0 <= i as int,
            acc as int == (i as int) * (i as int),
            i as int <= k as int,
        decreases (k as int) - (i as int)
    {
        acc = acc + (2 * i + 1);
        i = i + 1;
    }
    proof {
        lemma_min_jumps(n as int);
        assert(acc as int == min_jumps(n as int));
    }
    acc
}
// </vc-code>


}

fn main() {}