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
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
#[verifier::exec_allows_no_decreases_clause]
fn sum(s: &[int]) -> (a: int)
    requires s.len() > 0
    ensures sumcheck(s, s.len() as int) == a
// </vc-spec>
// <vc-code>
{
    proof {
        let tracked mut total: int = 0;
    }
    let mut i: usize = 0;
    while i < s.len()
        invariant
            0 <= i as int <= s.len() as int,
            total == sumcheck(s, i as int)
    {
        assert(sumcheck(s, (i as int) + 1) == s[i] + sumcheck(s, i as int));
        proof {
            total = total + s[i];
        }
        i += 1;
        // assert(total == sumcheck(s, i as int));  // This assert is redundant as the invariant ensures it after update
    }
    total
}
// </vc-code>

fn main() {
}

}