// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(a: int, b: int, c: int, d: int) -> bool {
    1 <= a <= 100 && 1 <= b <= 100 && 1 <= c <= 100 && 1 <= d <= 100
}

spec fn can_communicate(a: int, b: int, c: int, d: int) -> bool {
    (if a - c >= 0 { a - c } else { c - a }) <= d || 
    (((if a - b >= 0 { a - b } else { b - a }) <= d) && 
     ((if b - c >= 0 { b - c } else { c - b }) <= d))
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn solve(a: i8, b: i8, c: i8, d: i8) -> (result: String)
    requires 
        valid_input(a as int, b as int, c as int, d as int),
    ensures 
        result@ == seq!['Y', 'e', 's'] <==> can_communicate(a as int, b as int, c as int, d as int),
        result@ == seq!['Y', 'e', 's'] || result@ == seq!['N', 'o'],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Use String::new() with push_str to build result strings */
    let ac_dist = if a >= c { (a - c) as i8 } else { (c - a) as i8 };
    let ab_dist = if a >= b { (a - b) as i8 } else { (b - a) as i8 };
    let bc_dist = if b >= c { (b - c) as i8 } else { (c - b) as i8 };
    
    proof {
        assert(ac_dist as int == (if a as int - c as int >= 0 { a as int - c as int } else { c as int - a as int }));
        assert(ab_dist as int == (if a as int - b as int >= 0 { a as int - b as int } else { b as int - a as int }));
        assert(bc_dist as int == (if b as int - c as int >= 0 { b as int - c as int } else { c as int - b as int }));
    }
    
    let result = if ac_dist <= d {
        proof {
            assert((if a as int - c as int >= 0 { a as int - c as int } else { c as int - a as int }) <= d as int);
            assert(can_communicate(a as int, b as int, c as int, d as int));
        }
        let mut s = String::new();
        s.push_str("Yes");
        s
    } else if ab_dist <= d && bc_dist <= d {
        proof {
            assert((if a as int - b as int >= 0 { a as int - b as int } else { b as int - a as int }) <= d as int);
            assert((if b as int - c as int >= 0 { b as int - c as int } else { c as int - b as int }) <= d as int);
            assert(can_communicate(a as int, b as int, c as int, d as int));
        }
        let mut s = String::new();
        s.push_str("Yes");
        s
    } else {
        proof {
            assert(!((if a as int - c as int >= 0 { a as int - c as int } else { c as int - a as int }) <= d as int));
            assert(!((if a as int - b as int >= 0 { a as int - b as int } else { b as int - a as int }) <= d as int) || !((if b as int - c as int >= 0 { b as int - c as int } else { c as int - b as int }) <= d as int));
            assert(!can_communicate(a as int, b as int, c as int, d as int));
        }
        let mut s = String::new();
        s.push_str("No");
        s
    };
    
    result
}
// </vc-code>


}

fn main() {}