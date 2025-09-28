// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(s: int, v1: int, v2: int, t1: int, t2: int) -> bool
{
    1 <= s <= 1000 && 1 <= v1 <= 1000 && 1 <= v2 <= 1000 && 1 <= t1 <= 1000 && 1 <= t2 <= 1000
}

spec fn participant_time(s: int, v: int, t: int) -> int
{
    2 * t + s * v
}

spec fn correct_result(s: int, v1: int, v2: int, t1: int, t2: int) -> Seq<char>
{
    let time1 = participant_time(s, v1, t1);
    let time2 = participant_time(s, v2, t2);
    if time1 < time2 { seq!['F','i','r','s','t'] }
    else if time1 > time2 { seq!['S','e','c','o','n','d'] }
    else { seq!['F','r','i','e','n','d','s','h','i','p'] }
}

spec fn valid_result(result: Seq<char>) -> bool
{
    result == seq!['F','i','r','s','t'] || result == seq!['S','e','c','o','n','d'] || result == seq!['F','r','i','e','n','d','s','h','i','p']
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): [changed types to i32 to avoid potential overflow errors] */
fn compute_participant_time(s: i32, v: i32, t: i32) -> (time: i32)
    requires
        1 <= s <= 1000,
        1 <= v <= 1000,
        1 <= t <= 1000,
    ensures
        time == participant_time(s as int, v as int, t as int),
{
    2 * t + s * v
}
// </vc-helpers>

// <vc-spec>
fn solve(s: i8, v1: i8, v2: i8, t1: i8, t2: i8) -> (result: Vec<char>)
    requires 
        valid_input(s as int, v1 as int, v2 as int, t1 as int, t2 as int)
    ensures 
        valid_result(result@) &&
        result@ == correct_result(s as int, v1 as int, v2 as int, t1 as int, t2 as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): [updated casts to i32 to match helper signature] */
    let time1 = compute_participant_time(s as i32, v1 as i32, t1 as i32);
    let time2 = compute_participant_time(s as i32, v2 as i32, t2 as i32);

    if time1 < time2 {
        vec!['F','i','r','s','t']
    } else if time1 > time2 {
        vec!['S','e','c','o','n','d']
    } else {
        vec!['F','r','i','e','n','d','s','h','i','p']
    }
}
// </vc-code>


}

fn main() {}