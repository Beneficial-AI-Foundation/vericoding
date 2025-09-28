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
/* helper modified by LLM (iteration 5): add missing helpers and fix sequence syntax */
proof fn sum_of_odds_lemma(k: int)
    requires k >= 1,
    ensures seq_range(1, 2 * k, 2).sum() == k * k
{
    if k == 1 {
        assert(seq_range(1, 2, 2).sum() == 1);
    } else {
        sum_of_odds_lemma(k - 1);
        assert(seq_range(1, 2 * k, 2) =~= seq_range(1, 2 * (k - 1), 2).push(2 * k - 1));
        assert(seq_range(1, 2 * k, 2).sum() == seq_range(1, 2 * (k - 1), 2).sum() + (2 * k - 1));
        assert(seq_range(1, 2 * k, 2).sum() == (k - 1) * (k - 1) + (2 * k - 1));
        assert(seq_range(1, 2 * k, 2).sum() == k * k);
    }
}

spec fn seq_range(start: int, end: int, step: int) -> Seq<int>
    requires start <= end, step > 0
    decreases end - start
{
    if start >= end {
        Seq::empty()
    } else {
        seq_range(start + step, end, step).push(start)
    }
}

proof fn min_jumps_lemma(n: int)
    requires n >= 3,
    ensures (n - 2) * (n - 2) == seq_range(1, 2 * (n - 2) + 1, 2).sum()
{
    let k = n - 2;
    assert(2 * k + 1 == 2 * (n - 2) + 1);
    sum_of_odds_lemma(k);
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8) -> (result: i8)
    requires valid_input(n as int)
    ensures result as int == min_jumps(n as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): remove proof and use direct calculation */
    let k = (n - 2) as i8;
    k * k
}
// </vc-code>


}

fn main() {}