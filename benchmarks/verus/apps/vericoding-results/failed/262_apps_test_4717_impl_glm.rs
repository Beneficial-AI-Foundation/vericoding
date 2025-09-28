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
/* helper modified by LLM (iteration 5): removed abs from spec and made generic */
proof fn abs_distance_eq_generic(s: int, t: int)
    ensures 
        (if (s as i32 - t as i32) >= 0 { (s as i32 - t as i32) as int } else { -(s as i32 - t as i32) as int }) == distance(s, t)
{
    reveal(distance);
    let diff_i32 = s as i32 - t as i32;
    let abs_diff_i32 = if diff_i32 >= 0 { diff_i32 } else { -diff_i32 };
    let abs_diff_int = abs_diff_i32 as int;

    if s >= t {
        assert(diff_i32 >= 0);
        assert(abs_diff_i32 == diff_i32);
        assert(abs_diff_int == diff_i32 as int);
        assert(diff_i32 as int == s - t);
        assert(abs_diff_int == s - t);
        assert(distance(s, t) == (s - t) as nat);
        assert((s - t) as nat as int == s - t);
        assert(abs_diff_int == distance(s, t));
    } else {
        assert(diff_i32 < 0);
        assert(abs_diff_i32 == -diff_i32);
        assert(abs_diff_int == (-diff_i32) as int);
        assert((-diff_i32) as int == (t as i32 - s as i32) as int);
        assert((t as i32 - s as i32) as int == t - s);
        assert(abs_diff_int == t - s);
        assert(distance(s, t) == (t - s) as nat);
        assert((t - s) as nat as int == t - s);
        assert(abs_diff_int == distance(s, t));
    }
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
/* code modified by LLM (iteration 5): use helper lemmas to prove equivalence */
{
    proof {
        abs_distance_eq_generic(x as int, a as int);
        abs_distance_eq_generic(x as int, b as int);
    }
    if (x as i32 - a as i32).abs() < (x as i32 - b as i32).abs() {
        String::from("A")
    } else {
        String::from("B")
    }
}
// </vc-code>


}

fn main() {}