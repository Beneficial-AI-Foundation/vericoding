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
/* helper modified by LLM (iteration 5): Fix safe_add and safe_mul preconditions for 32-bit constraints */
fn safe_add(a: i32, b: i32) -> (c: i32)
    requires
        a >= -1000000 && a <= 1000000,
        b >= -1000000 && b <= 1000000,
        a + b >= i32::MIN,
        a + b <= i32::MAX,
    ensures
        c == a + b,
{
    a + b
}

fn safe_mul(a: i32, b: i32) -> (c: i32)
    requires
        a >= -1000 && a <= 1000,
        b >= -1000 && b <= 1000,
        a * b >= i32::MIN,
        a * b <= i32::MAX,
    ensures
        c == a * b,
{
    a * b
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
/* code modified by LLM (iteration 5): Use safe arithmetic with verified bounds from input */
{
    let s32 = s as i32;
    let v1_32 = v1 as i32;
    let v2_32 = v2 as i32;
    let t1_32 = t1 as i32;
    let t2_32 = t2 as i32;
    
    proof {
        assert(1 <= s32 && s32 <= 1000);
        assert(1 <= v1_32 && v1_32 <= 1000);
        assert(1 <= v2_32 && v2_32 <= 1000);
        assert(1 <= t1_32 && t1_32 <= 1000);
        assert(1 <= t2_32 && t2_32 <= 1000);
    }
    
    let term1 = safe_mul(2, t1_32);
    let term2 = safe_mul(s32, v1_32);
    let time1 = safe_add(term1, term2);
    
    let term3 = safe_mul(2, t2_32);
    let term4 = safe_mul(s32, v2_32);
    let time2 = safe_add(term3, term4);
    
    if time1 < time2 {
        vec!['F', 'i', 'r', 's', 't']
    } else if time1 > time2 {
        vec!['S', 'e', 'c', 'o', 'n', 'd']
    } else {
        vec!['F', 'r', 'i', 'e', 'n', 'd', 's', 'h', 'i', 'p']
    }
}
// </vc-code>


}

fn main() {}