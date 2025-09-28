use vstd::prelude::*;

verus! {

// sums from index 0 -> i - 1
spec fn sumcheck(s: &[int], i: int) -> int
    recommends 0 <= i <= s.len()
    decreases i when 0 <= i <= s.len()
{
    if i == 0 { 0 }
    else { s[i as nat - 1] + sumcheck(s, i - 1) }
}

// returns sum of array

// <vc-helpers>
fn sum_helper(s: &[int], i: int) -> int
    requires 0 <= i <= s.len() as int
    ensures sumcheck(s, i) == sum_helper(s, i) // This ensures clause is a bit redundant if sum_helper is meant to be the exact implementation of sumcheck. For verification, it's fine.
{
    if i == 0 {
        0
    } else {
        s[i as nat - 1] + sum_helper(s, i - 1)
    }
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
    let mut i: int = 0;
    let mut total_sum: int = 0;

    while i < s.len() as int
        invariant 0 <= i,
        invariant i <= s.len() as int,
        invariant total_sum == sumcheck(s, i),
    {
        total_sum = total_sum + s[i as nat];
        i = i + 1;
    }
    total_sum
}
// </vc-code>

fn main() {
}

}