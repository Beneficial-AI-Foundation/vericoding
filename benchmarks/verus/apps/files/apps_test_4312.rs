// <vc-preamble>
use vstd::prelude::*;

verus! {
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
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(a: i8, b: i8, c: i8, d: i8) -> (result: String)
    requires valid_input(a as int, b as int, c as int, d as int)
    ensures result@ == (if takahashi_wins(a as int, b as int, c as int, d as int) { "Yes"@ } else { "No"@ })
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}