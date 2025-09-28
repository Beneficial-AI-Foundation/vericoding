// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(n: int, m: int) -> bool {
    n >= 1 && m >= 1
}

spec fn optimal_vasya_score(n: int, m: int) -> int {
    if n < m { n } else { m }
}

spec fn optimal_petya_score(n: int, m: int) -> int {
    n + m - 1 - optimal_vasya_score(n, m)
}

spec fn total_adjacent_pairs(n: int, m: int) -> int {
    n + m - 1
}
// </vc-preamble>

// <vc-helpers>
proof fn lemma_optimal_scores_are_valid(n: int, m: int)
    ensures
        optimal_petya_score(n, m) + optimal_vasya_score(n, m) == total_adjacent_pairs(n, m),
{
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, m: i8) -> (result: (i8, i8))
    requires 
        valid_input(n as int, m as int)
    ensures 
        result.0 as int == optimal_petya_score(n as int, m as int) &&
        result.1 as int == optimal_vasya_score(n as int, m as int) &&
        result.0 as int + result.1 as int == total_adjacent_pairs(n as int, m as int)
// </vc-spec>
// <vc-code>
{
    let vasya: i8;
    let petya: i8;

    if n < m {
        petya = m - 1;
        vasya = n;
        proof {
            assert((n as int) < (m as int));
            assert(vasya as int == optimal_vasya_score(n as int, m as int));
            assert(petya as int == optimal_petya_score(n as int, m as int));
            assert(petya as int + vasya as int == total_adjacent_pairs(n as int, m as int));
        }
    } else {
        petya = n - 1;
        vasya = m;
        proof {
            assert((n as int) >= (m as int));
            assert(vasya as int == optimal_vasya_score(n as int, m as int));
            assert(petya as int == optimal_petya_score(n as int, m as int));
            assert(petya as int + vasya as int == total_adjacent_pairs(n as int, m as int));
        }
    }

    (petya, vasya)
}
// </vc-code>


}

fn main() {}