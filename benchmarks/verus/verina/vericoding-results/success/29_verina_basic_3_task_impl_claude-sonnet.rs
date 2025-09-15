// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn div_11_witness(n: i32) -> int { n / 11 }

proof fn divisible_by_11_lemma(n: i32)
    ensures (n % 11 == 0) <==> (exists|k: int| #[trigger] (k * 11) == n)
{
    if n % 11 == 0 {
        let k = n / 11;
        assert((k * 11) == n);
    } else {
        assert(forall|k: int| #[trigger] (k * 11) != n) by {
            assert(n % 11 != 0);
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn is_divisible_by_11(n: i32) -> (result: bool)
    ensures
        result <==> (exists|k: int| #[trigger] (k * 11) == n),
// </vc-spec>
// <vc-code>
{
    proof {
        divisible_by_11_lemma(n);
    }
    n % 11 == 0
}
// </vc-code>

}
fn main() {}