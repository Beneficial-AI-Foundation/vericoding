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
/* helper modified by LLM (iteration 5): relate i64 computed times to participant_time */
proof fn cast_ops(s: i8, v: i8, t: i8)
    ensures
        (2*(t as i64) + (s as i64)*(v as i64)) as int == participant_time(s as int, v as int, t as int),
{
    assert((2*(t as i64) + (s as i64)*(v as i64)) as int == 2*(t as int) + (s as int)*(v as int));
    assert(2*(t as int) + (s as int)*(v as int) == participant_time(s as int, v as int, t as int));
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
    /* code modified by LLM (iteration 5): compute times using i64, build result Vec<char>, and prove correctness using cast_ops */
    let time1_i64: i64 = 2*(t1 as i64) + (s as i64)*(v1 as i64);
    let time2_i64: i64 = 2*(t2 as i64) + (s as i64)*(v2 as i64);

    let mut result: Vec<char> = Vec::new();
    if time1_i64 < time2_i64 {
        result.push('F'); result.push('i'); result.push('r'); result.push('s'); result.push('t');
    } else if time1_i64 > time2_i64 {
        result.push('S'); result.push('e'); result.push('c'); result.push('o'); result.push('n'); result.push('d');
    } else {
        result.push('F'); result.push('r'); result.push('i'); result.push('e'); result.push('n'); result.push('d'); result.push('s'); result.push('h'); result.push('i'); result.push('p');
    }

    proof {
        cast_ops(s, v1, t1);
        cast_ops(s, v2, t2);
        assert((time1_i64 as int) == participant_time(s as int, v1 as int, t1 as int));
        assert((time2_i64 as int) == participant_time(s as int, v2 as int, t2 as int));
        if time1_i64 < time2_i64 {
            assert(result@ == seq!['F','i','r','s','t']);
        } else if time1_i64 > time2_i64 {
            assert(result@ == seq!['S','e','c','o','n','d']);
        } else {
            assert(result@ == seq!['F','r','i','e','n','d','s','h','i','p']);
        }
        assert(result@ == correct_result(s as int, v1 as int, v2 as int, t1 as int, t2 as int));
    }

    result
}

// </vc-code>


}

fn main() {}