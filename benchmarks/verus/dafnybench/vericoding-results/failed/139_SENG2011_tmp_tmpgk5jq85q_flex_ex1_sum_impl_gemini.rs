// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn sumcheck(s: &[int], i: int) -> int
    recommends 0 <= i <= s.len()
    decreases i when 0 <= i <= s.len()
{
    if i == 0 { 0 }
    else { s[i as nat - 1] + sumcheck(s, i - 1) }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed type mismatches with explicit literal types and casts */
proof fn calculate_sum_iteratively(s: &[int]) -> (total: int)
    ensures total == sumcheck(s, s.len() as int)
{
    let mut total: int = 0;
    let mut i: nat = 0;
    while i < s.len() as nat
        invariant
            0 <= i <= s.len() as nat,
            total == sumcheck(s, i as int),
        decreases (s.len() as nat) - i
    {
        assert(sumcheck(s, (i + 1) as int) == s@[i] + sumcheck(s, i as int)) by {
            reveal(sumcheck);
        };
        total = total + s@[i];
        i = i + 1;
    }
    total
}
// </vc-helpers>

// <vc-spec>
#[verifier::exec_allows_no_decreases_clause]
fn sum(s: &[int]) -> (a: int)
    requires s.len() > 0
    ensures sumcheck(s, s.len() as int) == a
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed type mismatches for loop counter and array indexing */
    let mut total: int = 0;
    let mut i: nat = 0;
    while i < s.len() as nat
        invariant
            0 <= i <= s.len() as nat,
            total == sumcheck(s, i as int),
    {
        proof {
            reveal(sumcheck);
        }
        total = total + s[i as usize];
        i = i + 1;
    }
    total
}
// </vc-code>

}
fn main() {}