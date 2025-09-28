// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn mod_11(n: int) -> int {
    n % 11
}

proof fn lemma_divisible_by_11(n: int)
    ensures
        (exists|k: int| #[trigger] (k * 11) == n) <==> (mod_11(n) == 0),
{
    if exists|k: int| #[trigger] (k * 11) == n {
        let k = choose|k: int| #[trigger] (k * 11) == n;
        assert(n == k * 11);
        assert(mod_11(n) == mod_11(k * 11));
        assert(mod_11(k * 11) == 0);
    }
    if mod_11(n) == 0 {
        let k = n / 11;
        assert(k * 11 == n);
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
    let remainder = n % 11;
    proof {
        lemma_divisible_by_11(n as int);
    }
    remainder == 0
}
// </vc-code>

}
fn main() {}