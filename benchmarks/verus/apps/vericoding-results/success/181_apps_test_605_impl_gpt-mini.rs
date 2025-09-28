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
/* helper modified by LLM (iteration 5): spec-level identity wrapper for calculate_score */
spec fn calculate_score_id(points: int, time: int) -> int {
    calculate_score(points, time)
}

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
    /* code modified by LLM (iteration 5): compute winner and prove relation to spec-level calculate_score */
    let a_i32 = a as i32;
    let b_i32 = b as i32;
    let c_i32 = c as i32;
    let d_i32 = d as i32;

    let min_m = 3 * a_i32 / 10;
    let time_adj_m = a_i32 - a_i32 * c_i32 / 250;
    let misha_score_i32 = if min_m >= time_adj_m { min_m } else { time_adj_m };

    let min_v = 3 * b_i32 / 10;
    let time_adj_v = b_i32 - b_i32 * d_i32 / 250;
    let vasya_score_i32 = if min_v >= time_adj_v { min_v } else { time_adj_v };

    let res = if misha_score_i32 > vasya_score_i32 {
        "Misha".to_string()
    } else if vasya_score_i32 > misha_score_i32 {
        "Vasya".to_string()
    } else {
        "Tie".to_string()
    };

    proof {
        let a_i = a as int;
        let b_i = b as int;
        let c_i = c as int;
        let d_i = d as int;

        let min_m_spec = 3 * a_i / 10;
        let time_adj_m_spec = a_i - a_i * c_i / 250;
        let misha_spec = if min_m_spec >= time_adj_m_spec { min_m_spec } else { time_adj_m_spec };

        let min_v_spec = 3 * b_i / 10;
        let time_adj_v_spec = b_i - b_i * d_i / 250;
        let vasya_spec = if min_v_spec >= time_adj_v_spec { min_v_spec } else { time_adj_v_spec };

        assert(misha_spec == calculate_score(a_i, c_i));
        assert(vasya_spec == calculate_score(b_i, d_i));

        assert(misha_spec == (misha_score_i32 as int));
        assert(vasya_spec == (vasya_score_i32 as int));

        if misha_spec > vasya_spec {
            assert(res@ == seq!['M','i','s','h','a']);
        } else if vasya_spec > misha_spec {
            assert(res@ == seq!['V','a','s','y','a']);
        } else {
            assert(res@ == seq!['T','i','e']);
        }
    }

    res
}

// </vc-code>


}

fn main() {}