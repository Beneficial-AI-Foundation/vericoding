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
proof fn lemma_distance_eval(s: int, t: int)
    ensures
        distance(s, t) == if s >= t { (s - t) as nat } else { (t - s) as nat },
{
    if s >= t {
        assert(distance(s, t) == (s - t) as nat);
    } else {
        assert(distance(s, t) == (t - s) as nat);
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
    let xi: int = x as int;
    let ai: int = a as int;
    let bi: int = b as int;

    let da: nat = if xi >= ai { (xi - ai) as nat } else { (ai - xi) as nat };
    let db: nat = if xi >= bi { (xi - bi) as nat } else { (bi - xi) as nat };

    proof {
        if xi >= ai {
            assert(da == (xi - ai) as nat);
            assert(distance(xi, ai) == da);
        } else {
            assert(da == (ai - xi) as nat);
            assert(distance(xi, ai) == da);
        }
        if xi >= bi {
            assert(db == (xi - bi) as nat);
            assert(distance(xi, bi) == db);
        } else {
            assert(db == (bi - xi) as nat);
            assert(distance(xi, bi) == db);
        }
    }

    if da < db {
        let result = String::from("A");
        proof {
            assert(distance(xi, ai) == da);
            assert(distance(xi, bi) == db);
            assert(da < db);
            assert(distance(xi, ai) < distance(xi, bi));
        }
        result
    } else {
        let result = String::from("B");
        proof {
            assert(distance(xi, ai) == da);
            assert(distance(xi, bi) == db);
            assert(distance(xi, ai) != distance(xi, bi));
            assert(!(da < db));
            assert(!(distance(xi, ai) < distance(xi, bi)));
            assert(distance(xi, bi) < distance(xi, ai));
        }
        result
    }
}
// </vc-code>


}

fn main() {}