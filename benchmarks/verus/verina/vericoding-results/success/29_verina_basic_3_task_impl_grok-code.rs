// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn is_divisible_by_11(n: i32) -> (result: bool)
    ensures
        result <==> (exists|k: int| #[trigger] (k * 11) == n),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): added proof block with witness for existential quantifier in divisibility check */
{
    let rem = n as i64 % 11;
    if rem == 0 {
        proof {
            assert((n as int) % 11 == 0);
            let k: int = (n as int) / 11;
            assert(k * 11 == n as int);
            assert((exists|k: int| #[trigger] (k * 11) == n as int));
        }
        return true;
    } else {
        return false;
    }
}
// </vc-code>

}
fn main() {}