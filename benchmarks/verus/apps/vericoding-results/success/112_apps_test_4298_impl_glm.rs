// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, d: int) -> bool {
    n >= 1 && n <= 20 && d >= 1 && d <= 20
}

spec fn coverage_range(position: int, d: int) -> (int, int) {
    (position - d, position + d)
}

spec fn trees_covered(n: int, d: int, inspectors: int) -> bool {
    inspectors >= 1 && inspectors <= n && inspectors == ((n - 1) / (2 * d + 1)) + 1
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn min_inspectors(n: i8, d: i8) -> (result: i8)
    requires valid_input(n as int, d as int)
    ensures trees_covered(n as int, d as int, result as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): remove helper function and use built-in properties to prove bounds */
    let k = 2 * d + 1;
    let result = ((n - 1) / k) + 1;
    proof {
        let n_int = n as int;
        let d_int = d as int;
        let k_int = 2 * d_int + 1;
        let a = n_int - 1;
        // Since a >= 0 and k_int >= 3, we have:
        //   a / k_int >= 0  => result >= 1
        //   a / k_int <= a   => result <= a + 1 = n_int
        assert(a >= 0);
        assert(k_int >= 3);
        assert(a / k_int >= 0);
        assert(a / k_int <= a);
        assert(result as int == a / k_int + 1);
        assert(1 <= result as int && result as int <= n_int);
        // The formula in trees_covered is exactly the one we used.
        assert(trees_covered(n_int, d_int, result as int));
    }
    result
}
// </vc-code>


}

fn main() {}