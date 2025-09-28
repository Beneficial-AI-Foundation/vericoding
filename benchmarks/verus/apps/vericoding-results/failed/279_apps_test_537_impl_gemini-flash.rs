// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, k: int) -> bool {
    n >= 0 && k >= 0 && k + 1 > 0
}

spec fn valid_output(result: Seq<int>, n: int, k: int) -> bool {
    result.len() == 3 &&
    result[0] >= 0 && result[1] >= 0 && result[2] >= 0 &&
    result[1] == result[0] * k &&
    result[0] + result[1] <= n / 2 &&
    result[2] == n - result[0] - result[1]
}

spec fn optimal_diplomas(n: int, k: int) -> int
    recommends valid_input(n, k)
{
    (n / 2) / (k + 1)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): add helper to check if an int is representable as an i8 */
spec fn is_i8_representable(val: int) -> bool {
    val >= i8::MIN as int && val <= i8::MAX as int
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, k: i8) -> (result: Vec<i8>)
    requires valid_input(n as int, k as int)
    ensures 
        valid_output(result@.map(|i, x| x as int), n as int, k as int) &&
        result@[0] as int == optimal_diplomas(n as int, k as int)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): moved ghost variables inside proof block */
{
    let x: i8;
    let y: i8;
    let z: i8;

    proof {
        let n_ghost: int = n as int;
        let k_ghost: int = k as int;

        let x_ghost: int = optimal_diplomas(n_ghost, k_ghost);
        let y_ghost: int = x_ghost * k_ghost;
        let z_ghost: int = n_ghost - x_ghost - y_ghost;

        assert(x_ghost >= 0);
        assert(y_ghost >= 0);
        assert(z_ghost >= 0) by {
            assert(valid_input(n_ghost, k_ghost));
            assert(x_ghost == (n_ghost / 2) / (k_ghost + 1));
            assert(x_ghost * (k_ghost + 1) <= n_ghost / 2);
            assert(x_ghost + y_ghost == x_ghost * (1 + k_ghost));
            assert(x_ghost + y_ghost <= n_ghost / 2);
            assert(n_ghost / 2 <= n_ghost);
            assert(x_ghost + y_ghost <= n_ghost);
            assert(z_ghost == n_ghost - (x_ghost + y_ghost));
        }

        assert(is_i8_representable(x_ghost));
        assert(is_i8_representable(y_ghost));
        assert(is_i8_representable(z_ghost));

        x = x_ghost as i8;
        y = y_ghost as i8;
        z = z_ghost as i8;
    }

    let mut result: Vec<i8> = Vec::new();
    result.push(x);
    result.push(y);
    result.push(z);
    result
}
// </vc-code>


}

fn main() {}