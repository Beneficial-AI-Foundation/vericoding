// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn power(x: int, n: nat) -> int
    decreases n
{
    if n == 0 { 1 } else { x * power(x, (n - 1) as nat) }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): added lemma to unfold power definition */
proof fn power_unfold(x: int, n: nat)
    requires n > 0
    ensures power(x, n) == x * power(x, (n - 1) as nat)
{
}
// </vc-helpers>

// <vc-spec>
fn power_iter(x: i64, n: u64) -> (p: i64)
    ensures p == power(x as int, n as nat)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): added proof block with lemma call */
    let mut p: i64 = 1;
    let mut i: u64 = 0;
    while i < n
        invariant
            p == power(x as int, i as nat),
            i <= n,
            forall|j: nat| (i as nat) <= j && j <= (n as nat) ==> i64::MIN <= #[trigger] power(x as int, j) <= i64::MAX,
        decreases n - i
    {
        proof {
            power_unfold(x as int, (i + 1) as nat);
        }
        p = p * x;
        i = i + 1;
    }
    p
}
// </vc-code>

}
fn main() {}