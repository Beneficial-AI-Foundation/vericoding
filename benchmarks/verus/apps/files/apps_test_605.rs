// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn valid_input(a: int, b: int, c: int, d: int) -> bool {
    250 <= a <= 3500 && a % 250 == 0 &&
    250 <= b <= 3500 && b % 250 == 0 &&
    0 <= c <= 180 &&
    0 <= d <= 180
}

spec fn calculate_score(points: int, time: int) -> int {
    let min_score = 3 * points / 10;
    let time_adjusted = points - points * time / 250;
    if min_score >= time_adjusted { min_score } else { time_adjusted }
}

spec fn correct_result(a: int, b: int, c: int, d: int, result: String) -> bool {
    let misha_score = calculate_score(a, c);
    let vasya_score = calculate_score(b, d);
    (result == "Misha" <==> misha_score > vasya_score) &&
    (result == "Vasya" <==> vasya_score > misha_score) &&
    (result == "Tie" <==> misha_score == vasya_score)
}
// </vc-helpers>

// <vc-spec>
fn determine_winner(a: int, b: int, c: int, d: int) -> (result: String)
    requires valid_input(a, b, c, d)
    ensures result@ == "Misha" || result@ == "Vasya" || result@ == "Tie"
    ensures correct_result(a, b, c, d, result)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}