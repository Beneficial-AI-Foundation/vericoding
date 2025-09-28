// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(x: int, a: int, b: int) -> bool {
    1 <= x <= 1000 &&
    1 <= a <= 1000 &&
    1 <= b <= 1000 &&
    x != a && x != b && a != b &&
    distance(x, a) != distance(x, b)
}

spec fn distance(s: int, t: int) -> nat {
    if s >= t { (s - t) as nat } else { (t - s) as nat }
}

spec fn correct_result(x: int, a: int, b: int, result: Seq<char>) -> bool {
    (result == seq!['A'] <==> distance(x, a) < distance(x, b)) &&
    (result == seq!['B'] <==> distance(x, b) < distance(x, a))
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn solve(x: i8, a: i8, b: i8) -> (result: String)
    requires 
        valid_input(x as int, a as int, b as int),
    ensures 
        result@ == seq!['A'] || result@ == seq!['B'],
        correct_result(x as int, a as int, b as int, result@),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Using String::from() which is supported in Verus instead of String::new() */
    let dist_xa: i8 = if x >= a { x - a } else { a - x };
    let dist_xb: i8 = if x >= b { x - b } else { b - x };
    
    proof {
        assert(dist_xa as int == distance(x as int, a as int));
        assert(dist_xb as int == distance(x as int, b as int));
    }
    
    let result = if dist_xa < dist_xb {
        proof {
            assert(distance(x as int, a as int) < distance(x as int, b as int));
            assert(correct_result(x as int, a as int, b as int, seq!['A']));
        }
        String::from("A")
    } else {
        proof {
            assert(distance(x as int, b as int) < distance(x as int, a as int));
            assert(correct_result(x as int, a as int, b as int, seq!['B']));
        }
        String::from("B")
    };
    
    result
}
// </vc-code>


}

fn main() {}