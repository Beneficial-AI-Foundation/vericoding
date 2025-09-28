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
    /* code modified by LLM (iteration 2): fixed compilation errors by using i32 for calculations in executable code */
    let aoki_turns = ((a as i32) + (d as i32) - 1) / (d as i32);
    let takahashi_turns = ((c as i32) + (b as i32) - 1) / (b as i32);
    let result_str = if aoki_turns >= takahashi_turns { "Yes".to_string() } else { "No".to_string() };
    result_str
}
// </vc-code>


}

fn main() {}