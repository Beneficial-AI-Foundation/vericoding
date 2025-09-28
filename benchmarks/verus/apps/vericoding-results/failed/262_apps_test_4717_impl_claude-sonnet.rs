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
/* helper modified by LLM (iteration 5): changed function to proof fn to fix exec mode call error */
proof fn lemma_distance_properties(x: int, a: int, b: int)
    requires
        1 <= x <= 1000,
        1 <= a <= 1000,
        1 <= b <= 1000,
        x != a && x != b && a != b,
        distance(x, a) != distance(x, b),
    ensures
        distance(x, a) < distance(x, b) || distance(x, b) < distance(x, a),
{}

proof fn lemma_distance_abs(s: int, t: int)
    requires
        1 <= s <= 1000,
        1 <= t <= 1000,
    ensures
        distance(s, t) == if s >= t { (s - t) as nat } else { (t - s) as nat },
        distance(s, t) >= 0,
{}
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
    /* code modified by LLM (iteration 5): fixed lemma call in proof block */
    let dist_a = if x >= a { (x - a) as u32 } else { (a - x) as u32 };
    let dist_b = if x >= b { (x - b) as u32 } else { (b - x) as u32 };
    
    proof {
        assert(dist_a == distance(x as int, a as int));
        assert(dist_b == distance(x as int, b as int));
        lemma_distance_properties(x as int, a as int, b as int);
    }
    
    if dist_a < dist_b {
        proof {
            assert(distance(x as int, a as int) < distance(x as int, b as int));
        }
        "A".to_string()
    } else {
        proof {
            assert(distance(x as int, b as int) < distance(x as int, a as int));
        }
        "B".to_string()
    }
}
// </vc-code>


}

fn main() {}