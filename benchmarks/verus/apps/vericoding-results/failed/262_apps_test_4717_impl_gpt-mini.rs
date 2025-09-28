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
/* helper modified by LLM (iteration 5): string_of_char constructs a String from a single-character sequence */
fn string_of_char(c: char) -> (s: String)
    ensures
        s@ == seq![c],
{
    if c == 'A' {
        vstd::string::string_from_str("A")
    } else {
        vstd::string::string_from_str("B")
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
{
    /* code modified by LLM (iteration 5): use ghost ints for specs, compute distances with machine ints, return single-char String via helper */
    ghost let xi: int = x as int;
    ghost let ai: int = a as int;
    ghost let bi: int = b as int;

    let da: i32 = if x >= a { (x - a) as i32 } else { (a - x) as i32 };
    let db: i32 = if x >= b { (x - b) as i32 } else { (b - x) as i32 };

    let result: String = if da < db { string_of_char('A') } else { string_of_char('B') };

    proof {
        assert(distance(xi, ai) == if xi >= ai { (xi - ai) as nat } else { (ai - xi) as nat });
        assert(distance(xi, bi) == if xi >= bi { (xi - bi) as nat } else { (bi - xi) as nat });
        assert(distance(xi, ai) != distance(xi, bi));

        if da < db {
            assert(result@ == seq!['A']);
            assert((da as nat) < (db as nat));
            assert(distance(xi, ai) < distance(xi, bi));
            assert(correct_result(xi, ai, bi, result@));
        } else {
            assert(result@ == seq!['B']);
            assert((db as nat) < (da as nat));
            assert(distance(xi, bi) < distance(xi, ai));
            assert(correct_result(xi, ai, bi, result@));
        }
    }

    result
}
// </vc-code>


}

fn main() {}