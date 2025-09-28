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
/* helper modified by LLM (iteration 5): recursive spec helper returning popcount(n) */
spec fn compute_popcount(n: nat) -> (result: nat)
    ensures
        result == popcount(n),
    decreases n
{
    if n == 0 {
        0
    } else {
        (n % 2) + compute_popcount(n / 2)
    }
}
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
    /* code modified by LLM (iteration 5): compute popcount for each element using spec helper */
    let tracked mut result: Vec<nat> = Vec::new();
    let n: int = x.len();
    let mut i: int = 0;
    while i < n
        invariant
            0 <= i <= n,
            result.len() == i,
            forall|j: int| 0 <= j < result.len() ==> result[j] == popcount(abs_spec(x[j])),
        decreases n - i
    {
        let xi: i32 = x[i];
        let ghost a: nat = abs_spec(xi);
        let ghost pc: nat = compute_popcount(a);
        proof {
            assert(popcount(abs_spec(xi)) == popcount(a));
            assert(pc == popcount(a));
            assert(pc == popcount(abs_spec(xi)));
        }
        result.push(pc);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}