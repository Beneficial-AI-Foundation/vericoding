// <vc-preamble>
use vstd::prelude::*;

verus! {
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

spec fn correct_result(a: int, b: int, c: int, d: int, result: Seq<char>) -> bool {
    let misha_score = calculate_score(a, c);
    let vasya_score = calculate_score(b, d);
    (result == seq!['M','i','s','h','a'] <==> misha_score > vasya_score) &&
    (result == seq!['V','a','s','y','a'] <==> vasya_score > misha_score) &&
    (result == seq!['T','i','e'] <==> misha_score == vasya_score)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn determine_winner(a: int, b: int, c: int, d: int) -> (result: String)
    requires 
        valid_input(a, b, c, d)
    ensures 
        result@ == seq!['M','i','s','h','a'] || result@ == seq!['V','a','s','y','a'] || result@ == seq!['T','i','e'],
        correct_result(a, b, c, d, result@)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}