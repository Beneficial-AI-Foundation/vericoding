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
/* helper modified by LLM (iteration 5): empty */

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
/* code modified by LLM (iteration 5): remove invalid by() syntax in asserts */
{
    proof {
        assert(1 <= s as int <= 1000);
        assert(1 <= v1 as int <= 1000);
        assert(1 <= v2 as int <= 1000);
        assert(1 <= t1 as int <= 1000);
        assert(1 <= t2 as int <= 1000);
        assert(s as i32 == s as int);
        assert(v1 as i32 == v1 as int);
        assert(v2 as i32 == v2 as int);
        assert(t1 as i32 == t1 as int);
        assert(t2 as i32 == t2 as int);
    }
    let s32: i32 = s as i32;
    let v1_32: i32 = v1 as i32;
    let v2_32: i32 = v2 as i32;
    let t1_32: i32 = t1 as i32;
    let t2_32: i32 = t2 as i32;
    let time1: i32 = 2 * t1_32 + s32 * v1_32;
    let time2: i32 = 2 * t2_32 + s32 * v2_32;
    if time1 < time2 {
        let mut res = Vec::new();
        res.push('F');
        res.push('i');
        res.push('r');
        res.push('s');
        res.push('t');
        res
    } else if time1 > time2 {
        let mut res = Vec::new();
        res.push('S');
        res.push('e');
        res.push('c');
        res.push('o');
        res.push('n');
        res.push('d');
        res
    } else {
        let mut res = Vec::new();
        res.push('F');
        res.push('r');
        res.push('i');
        res.push('e');
        res.push('n');
        res.push('d');
        res.push('s');
        res.push('h');
        res.push('i');
        res.push('p');
        res
    }
}
// </vc-code>


}

fn main() {}