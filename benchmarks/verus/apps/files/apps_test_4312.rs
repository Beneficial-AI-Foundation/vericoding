// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn valid_input(a: int, b: int, c: int, d: int) -> bool {
    1 <= a <= 100 && 1 <= b <= 100 && 1 <= c <= 100 && 1 <= d <= 100
}

spec fn turns_to_defeat(health: int, strength: int) -> int
    recommends strength > 0
{
    (health + strength - 1) / strength
}

spec fn takahashi_wins(a: int, b: int, c: int, d: int) -> bool
    recommends valid_input(a, b, c, d)
{
    let takahashi_turns = turns_to_defeat(c, b);
    let aoki_turns = turns_to_defeat(a, d);
    aoki_turns >= takahashi_turns
}
// </vc-helpers>

// <vc-spec>
fn solve(a: int, b: int, c: int, d: int) -> (result: String)
    requires valid_input(a, b, c, d)
    ensures result@ == (if takahashi_wins(a, b, c, d) { "Yes"@ } else { "No"@ })
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}