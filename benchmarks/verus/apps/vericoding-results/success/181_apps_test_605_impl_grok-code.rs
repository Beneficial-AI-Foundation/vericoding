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
fn determine_winner(a: i8, b: i8, c: i8, d: i8) -> (result: String)
    requires 
        valid_input(a as int, b as int, c as int, d as int)
    ensures 
        result@ == seq!['M','i','s','h','a'] || result@ == seq!['V','a','s','y','a'] || result@ == seq!['T','i','e'],
        correct_result(a as int, b as int, c as int, d as int, result@)
// </vc-spec>
// <vc-code>
{
    let misha_points: i32 = a as i32;
    let vasya_points: i32 = b as i32;
    let c_time: i32 = c as i32;
    let d_time: i32 = d as i32;
    let min_score_m: i32 = 3 * misha_points / 10;
    let time_adj_m: i32 = misha_points - misha_points * c_time / 250;
    let misha_score: i32 = if min_score_m >= time_adj_m { min_score_m } else { time_adj_m };
    let min_score_v: i32 = 3 * vasya_points / 10;
    let time_adj_v: i32 = vasya_points - vasya_points * d_time / 250;
    let vasya_score: i32 = if min_score_v >= time_adj_v { min_score_v } else { time_adj_v };
    if misha_score > vasya_score {
        "Misha".to_string()
    } else if vasya_score > misha_score {
        "Vasya".to_string()
    } else {
        "Tie".to_string()
    }
}
// </vc-code>


}

fn main() {}