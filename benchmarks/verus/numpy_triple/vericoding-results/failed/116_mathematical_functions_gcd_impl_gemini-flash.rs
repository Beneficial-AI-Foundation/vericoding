// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Renamed `gcd` to `gcd_recursive` to avoid redefinition error. */
spec fn gcd_recursive(a: int, b: int) -> int {
    if b == 0 {
        int_abs(a)
    } else {
        gcd_recursive(b, a % b)
    }
}
// </vc-helpers>

// <vc-spec>
#[verifier::external_body]
spec fn gcd(a: int, b: int) -> int {
    unimplemented!()
}

spec fn int_abs(x: int) -> int {
    if x >= 0 { x } else { -x }
}

fn numpy_gcd(x1: Vec<i8>, x2: Vec<i8>) -> (result: Vec<i8>)
    requires x1@.len() == x2@.len(),
    ensures
        result@.len() == x1@.len(),
        forall|i: int| 0 <= i < result@.len() ==> #[trigger] result@[i] as int == gcd(x1@[i] as int, x2@[i] as int),
        forall|i: int| 0 <= i < result@.len() ==> #[trigger] result@[i] >= 0,
        forall|i: int| 0 <= i < result@.len() ==> gcd(x1@[i] as int, x2@[i] as int) == #[trigger] gcd(int_abs(x1@[i] as int), int_abs(x2@[i] as int)),
        forall|i: int| 0 <= i < result@.len() ==> (x1@[i] == 0 && x2@[i] == 0) ==> #[trigger] result@[i] == 0,
        forall|i: int| 0 <= i < result@.len() ==> (x1@[i] != 0 && x2@[i] == 0) ==> #[trigger] result@[i] as int == int_abs(x1@[i] as int),
        forall|i: int| 0 <= i < result@.len() ==> (x1@[i] == 0 && x2@[i] != 0) ==> #[trigger] result@[i] as int == int_abs(x2@[i] as int),
        forall|i: int| 0 <= i < result@.len() ==> #[trigger] (result@[i] as int) % (x1@[i] as int) == 0 && (result@[i] as int) % (x2@[i] as int) == 0,
        forall|i: int| 0 <= i < result@.len() ==> gcd(x2@[i] as int, x1@[i] as int) == #[trigger] gcd(x1@[i] as int, x2@[i] as int),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Corrected call to `gcd_recursive` and ensured all values are `int` for gcd calculation. Removed `as int` casts for `nat` and `int` types in ghost code. */
{
    let mut result_vec: Vec<i8> = Vec::new();
    let len = x1@.len();

    let mut i: int = 0;
    while i < len
        invariant
            0 <= i <= len,
            result_vec.len() == i as nat,
            forall|j: int| 0 <= j < i ==> #[trigger] result_vec@[j] as int == gcd_recursive(x1@[j] as int, x2@[j] as int),
            forall|j: int| 0 <= j < i ==> #[trigger] result_vec@[j] >= 0,
    {
        proof {
            assert(gcd_recursive(x1@[i] as int, x2@[i] as int) == gcd_recursive(x1@[i] as int, x2@[i] as int));
        }

        let current_gcd = gcd_recursive(x1@[i] as int, x2@[i] as int);
        result_vec.push(current_gcd as i8);
        i = i + 1;
    }

    result_vec
}
// </vc-code>

}
fn main() {}