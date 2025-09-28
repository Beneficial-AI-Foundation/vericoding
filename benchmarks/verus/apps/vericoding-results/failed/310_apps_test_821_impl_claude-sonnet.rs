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
/* helper modified by LLM (iteration 5): fixed overflow assertion with i8 bounds */
fn calculate_time(s: i8, v: i8, t: i8) -> (time: i32)
    requires
        1 <= s <= 1000,
        1 <= v <= 1000,
        1 <= t <= 1000
    ensures
        time == participant_time(s as int, v as int, t as int)
{
    proof {
        assert(2 * (t as int) <= 2000);
        assert((s as int) <= 127);
        assert((v as int) <= 127);
        assert((s as int) * (v as int) <= 127 * 127);
        assert(127 * 127 == 16129);
        assert(2 * (t as int) + (s as int) * (v as int) <= 2000 + 16129);
        assert(18129 <= 2147483647);
    }
    let t_part = 2i32 * (t as i32);
    let sv_part = (s as i32) * (v as i32);
    t_part + sv_part
}

fn create_first() -> (result: Vec<char>)
    ensures
        result@ == seq!['F','i','r','s','t']
{
    let mut result = Vec::new();
    result.push('F');
    result.push('i');
    result.push('r');
    result.push('s');
    result.push('t');
    result
}

fn create_second() -> (result: Vec<char>)
    ensures
        result@ == seq!['S','e','c','o','n','d']
{
    let mut result = Vec::new();
    result.push('S');
    result.push('e');
    result.push('c');
    result.push('o');
    result.push('n');
    result.push('d');
    result
}

fn create_friendship() -> (result: Vec<char>)
    ensures
        result@ == seq!['F','r','i','e','n','d','s','h','i','p']
{
    let mut result = Vec::new();
    result.push('F');
    result.push('r');
    result.push('i');
    result.push('e');
    result.push('n');
    result.push('d');
    result.push('s');
    result.push('h');
    result.push('i');
    result.push('p');
    result
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
    /* code modified by LLM (iteration 5): added proof about i8 bounds */
    proof {
        assert(1 <= s <= 1000);
        assert(1 <= v1 <= 1000);
        assert(1 <= v2 <= 1000);
        assert(1 <= t1 <= 1000);
        assert(1 <= t2 <= 1000);
        assert(s <= 127);
        assert(v1 <= 127);
        assert(v2 <= 127);
        assert(t1 <= 127);
        assert(t2 <= 127);
    }
    
    let time1 = calculate_time(s, v1, t1);
    let time2 = calculate_time(s, v2, t2);
    
    if time1 < time2 {
        create_first()
    } else if time1 > time2 {
        create_second()
    } else {
        create_friendship()
    }
}
// </vc-code>


}

fn main() {}