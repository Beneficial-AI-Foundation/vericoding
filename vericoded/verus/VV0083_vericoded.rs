// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): no-op helper for divisibility proofs */
proof fn div_by_11_helper() {
}

// </vc-helpers>

// <vc-spec>
fn is_divisible_by_11(n: i32) -> (result: bool)
    ensures
        result <==> (exists|k: int| #[trigger] (k * 11) == n),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): compute divisibility using remainder and prove existence when divisible */
    let result: bool = n % 11 == 0;
    proof {
        if result {
            let k: int = (n / 11) as int;
            assert(k * 11 == n as int);
            assert(exists|k: int| #[trigger] (k * 11) == n as int);
        }
    }
    result
}
// </vc-code>

}
fn main() {}