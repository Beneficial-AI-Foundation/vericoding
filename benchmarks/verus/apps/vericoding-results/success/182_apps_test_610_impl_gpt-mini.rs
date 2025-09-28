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
/* helper modified by LLM (iteration 5): characterize optimal_petya_score as max-1 */
proof fn lemma_petya_max_minus_one(n: int, m: int)
    requires
        valid_input(n, m),
    ensures
        optimal_petya_score(n, m) == if n < m { m - 1 } else { n - 1 },
{
    if n < m {
        assert(optimal_vasya_score(n, m) == n);
        assert(optimal_petya_score(n, m) == n + m - 1 - n);
        assert(optimal_petya_score(n, m) == m - 1);
    } else {
        assert(optimal_vasya_score(n, m) == m);
        assert(optimal_petya_score(n, m) == n + m - 1 - m);
        assert(optimal_petya_score(n, m) == n - 1);
    }
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
    /* code modified by LLM (iteration 5): compute vasya and petya using widened integer to avoid overflow and prove spec equivalence */
    let vasya: i8 = if n < m { n } else { m };
    let petya_i16: i16 = (n as i16) + (m as i16) - 1 - (vasya as i16);
    proof {
        assert((vasya as int) == optimal_vasya_score(n as int, m as int));
        assert((petya_i16 as int) == (n as int) + (m as int) - 1 - (vasya as int));
        assert((petya_i16 as int) == optimal_petya_score(n as int, m as int));
        assert((petya_i16 as int) <= i8::MAX as int);
        assert((petya_i16 as int) >= i8::MIN as int);
    }
    let petya: i8 = petya_i16 as i8;
    (petya, vasya)
}

// </vc-code>


}

fn main() {}