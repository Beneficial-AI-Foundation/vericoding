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
proof fn lemma_valid_input_bounds(a: int, b: int, c: int, d: int)
    requires valid_input(a, b, c, d)
    ensures 1 <= a <= 100 && 1 <= b <= 100 && 1 <= c <= 100 && 1 <= d <= 100
{
    assert(valid_input(a, b, c, d));
}
/* helper modified by LLM (iteration 5): Added lemma for input bounds */
// </vc-helpers>

// <vc-spec>
fn solve(a: i8, b: i8, c: i8, d: i8) -> (result: String)
    requires valid_input(a as int, b as int, c as int, d as int)
    ensures result@ == (if takahashi_wins(a as int, b as int, c as int, d as int) { "Yes"@ } else { "No"@ })
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed function call and proof structure */
{
    proof {
        lemma_valid_input_bounds(a as int, b as int, c as int, d as int);
        assert(1 <= b as int <= 100);
        assert(1 <= d as int <= 100);
    }
    
    let takahashi_turns = ((c as u16 + b as u16 - 1) / b as u16) as u8;
    let aoki_turns = ((a as u16 + d as u16 - 1) / d as u16) as u8;
    
    if takahashi_turns <= aoki_turns {
        "Yes".to_string()
    } else {
        "No".to_string()
    }
}
// </vc-code>


}

fn main() {}