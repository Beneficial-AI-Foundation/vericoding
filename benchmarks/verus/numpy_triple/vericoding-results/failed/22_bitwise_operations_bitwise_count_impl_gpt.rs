// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn abs_spec(x: i32) -> nat {
    if x >= 0 { x as nat } else { (-x) as nat }
}

spec fn popcount(n: nat) -> nat 
    decreases n
{
    if n == 0 {
        0
    } else {
        (n % 2) + popcount(n / 2)
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): simple spec bridge to popcount */
spec fn compute_popcount_nat(n: nat) -> nat { popcount(n) }
// </vc-helpers>

// <vc-spec>
fn bitwise_count(x: Vec<i32>) -> (result: Vec<nat>)
    ensures
        result.len() == x.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == popcount(abs_spec(x[i])),
        forall|i: int| 0 <= i < result.len() ==> x[i] == 0 ==> result[i] == 0,
        forall|i: int| 0 <= i < result.len() ==> result[i] >= 0,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): avoid ghost indexing in exec; use x[i] instead of x@[i as int] */
    let n = x.len();
    let mut out: Vec<nat> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            out.len() == i,
            i <= n,
            forall|k: int| 0 <= k < i as int ==> out@[k] == popcount(abs_spec(x[k])),
        decreases n - i
    {
        let c: nat = popcount(abs_spec(x[i]));
        out.push(c);
        i = i + 1;
    }
    out
}
// </vc-code>

}
fn main() {}