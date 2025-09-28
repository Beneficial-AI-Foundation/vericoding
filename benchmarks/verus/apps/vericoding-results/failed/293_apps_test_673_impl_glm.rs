// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, k: int) -> bool {
    n >= 1 && k > 0
}

spec fn is_correct_result(n: int, k: int, result: int) -> bool 
    recommends k > 0
{
    result > n && result % k == 0 && forall|x: int| n < x < result ==> #[trigger] (x % k) != 0
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): fixed ensures syntax */
proof fn lemma_next_multiple_bound(n: int, k: int)
    requires
        n >= 1,
        k > 0,
    ensures
        ((n + k) / k) * k <= n + k
{
    let q = (n + k) / k;
    let r = (n + k) % k;
    assert(n + k == q * k + r && 0 <= r < k);
    let result = q * k;
    assert(result == (n + k) - r);
    assert(result <= n + k);
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, k: i8) -> (result: i8)
    requires valid_input(n as int, k as int)
    ensures is_correct_result(n as int, k as int, result as int)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): fixed quantifier syntax and condition */
{
    let result_int = ((n as int + k as int) / (k as int)) * (k as int);
    let result = result_int as i8;
    proof {
        lemma_next_multiple_bound(n as int, k as int);

        // Prove result_int > n
        let q_prev = (n as int) / (k as int);
        let r = (n as int) % (k as int);
        assert(0 <= r < k as int);
        assert(n as int == q_prev * (k as int) + r);
        let q = (n as int + k as int) / (k as int);
        assert(q == q_prev + 1);
        assert(result_int == q * (k as int));
        assert(result_int == (q_prev+1) * (k as int));
        assert(result_int == (n as int) - r + (k as int));
        assert(result_int > n as int);

        // Prove result_int % k == 0
        assert(result_int % (k as int) == 0);

        // Prove there is no multiple between n and result_int
        assert(forall|x: int| n as int < x < result_int ==> x % (k as int) != 0) by {
            let x = arbitrary;
            if (n as int < x) && (x < result_int) {
                let m = x / (k as int);
                let r_x = x % (k as int);
                assert(x == m * (k as int) + r_x && 0<=r_x<k as int);
                if r_x == 0 {
                    // Then x is a multiple of k. We show that x must be at least result_int.
                    assert(m >= q_prev+1);
                    assert(x >= (q_prev+1) * (k as int));
                    assert(x >= result_int);
                    // But we have x < result_int, so this is a contradiction.
                    assert(false);
                }
            }
        }
    }
    result
}
// </vc-code>


}

fn main() {}