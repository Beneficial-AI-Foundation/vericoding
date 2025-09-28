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
/* helper modified by LLM (iteration 5): changed return type to nat to match spec instead of i32 */
fn exec_distance(x: i32, a: i32) -> (result: nat)
    requires
        1 <= x <= 1000,
        1 <= a <= 1000,
    ensures
        result == distance(x as int, a as int),
{
    if x >= a { (x - a) as nat } else { (a - x) as nat }
}
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
    /* code modified by LLM (iteration 5): compute distances as nat and compare directly, added proof blocks in branches to help verification */
    let x_int = x as i32;
    let a_int = a as i32;
    let b_int = b as i32;
    let dist_a = exec_distance(x_int, a_int);
    let dist_b = exec_distance(x_int, b_int);
    if dist_a < dist_b {
        proof {
            assert(distance(x as int, a as int) < distance(x as int, b as int));
        }
        "A".to_string()
    } else {
        proof {
            assert(distance(x as int, a as int) > distance(x as int, b as int));
        }
        "B".to_string()
    }
}
// </vc-code>


}

fn main() {}