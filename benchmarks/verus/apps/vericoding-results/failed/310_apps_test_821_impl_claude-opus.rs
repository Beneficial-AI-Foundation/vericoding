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
    /* code modified by LLM (iteration 5): added explicit proof steps for multiplication bounds */
    proof {
        assert(1 <= s as int <= 1000);
        assert(1 <= v1 as int <= 1000);
        assert(1 <= v2 as int <= 1000);
        assert(1 <= t1 as int <= 1000);
        assert(1 <= t2 as int <= 1000);
        
        // Help Verus understand the multiplication bounds
        assert(s as int <= 1000);
        assert(v1 as int <= 1000);
        assert(s as int * v1 as int <= s as int * 1000) by {
            assert(v1 as int <= 1000);
        }
        assert(s as int * 1000 <= 1000 * 1000) by {
            assert(s as int <= 1000);
        }
        assert((s as int) * (v1 as int) <= 1000 * 1000);
        
        assert(s as int <= 1000);
        assert(v2 as int <= 1000);
        assert(s as int * v2 as int <= s as int * 1000) by {
            assert(v2 as int <= 1000);
        }
        assert(s as int * 1000 <= 1000 * 1000) by {
            assert(s as int <= 1000);
        }
        assert((s as int) * (v2 as int) <= 1000 * 1000);
        
        assert(2 * (t1 as int) <= 2000);
        assert(2 * (t1 as int) + (s as int) * (v1 as int) <= 1002000);
        assert(2 * (t2 as int) <= 2000);
        assert(2 * (t2 as int) + (s as int) * (v2 as int) <= 1002000);
    }
    
    let time1 = 2 * (t1 as i32) + (s as i32) * (v1 as i32);
    let time2 = 2 * (t2 as i32) + (s as i32) * (v2 as i32);
    
    if time1 < time2 {
        let mut result = Vec::new();
        result.push('F');
        result.push('i');
        result.push('r');
        result.push('s');
        result.push('t');
        proof {
            assert(result@ == seq!['F','i','r','s','t']);
            assert(time1 as int == participant_time(s as int, v1 as int, t1 as int));
            assert(time2 as int == participant_time(s as int, v2 as int, t2 as int));
        }
        result
    } else if time1 > time2 {
        let mut result = Vec::new();
        result.push('S');
        result.push('e');
        result.push('c');
        result.push('o');
        result.push('n');
        result.push('d');
        proof {
            assert(result@ == seq!['S','e','c','o','n','d']);
            assert(time1 as int == participant_time(s as int, v1 as int, t1 as int));
            assert(time2 as int == participant_time(s as int, v2 as int, t2 as int));
        }
        result
    } else {
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
        proof {
            assert(result@ == seq!['F','r','i','e','n','d','s','h','i','p']);
            assert(time1 as int == participant_time(s as int, v1 as int, t1 as int));
            assert(time2 as int == participant_time(s as int, v2 as int, t2 as int));
        }
        result
    }
}
// </vc-code>


}

fn main() {}