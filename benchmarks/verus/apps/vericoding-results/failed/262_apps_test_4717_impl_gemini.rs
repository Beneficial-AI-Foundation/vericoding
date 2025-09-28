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
/* helper modified by LLM (iteration 5): [no changes needed] */
fn compute_distance(s: i8, t: i8) -> (dist: u8)
    ensures
        dist as nat == distance(s as int, t as int),
{
    let s_int = s as i16;
    let t_int = t as i16;
    if s_int >= t_int {
        (s_int - t_int) as u8
    } else {
        (t_int - s_int) as u8
    }
}

/* helper modified by LLM (iteration 5): [no changes needed] */
proof fn lemma_u8_nat_lt(a: u8, b: u8, a_nat: nat, b_nat: nat)
    requires
        a as nat == a_nat,
        b as nat == b_nat,
    ensures
        (a < b) == (a_nat < b_nat),
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
    /* code modified by LLM (iteration 5): [wrapped ghost code in a proof block] */
    let dist_a = compute_distance(x, a);
    let dist_b = compute_distance(x, b);

    proof {
        lemma_u8_nat_lt(dist_a, dist_b, distance(x as int, a as int), distance(x as int, b as int));
    }

    if dist_a < dist_b {
        String::from_str("A")
    } else {
        String::from_str("B")
    }
}
// </vc-code>


}

fn main() {}